-- Prove2me | Theorems.Thm_QDSGibbs_Supplement_theorem_1_1
-- name    : QDSGibbs.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:31:01.098929+00:00
-- url     : https://prove2.me/theorems/ef22f99b-16b3-4e0a-95f1-196f3ba517b6
-- title:
--   Theorem 1.1 — weakly interacting Fermi–Hubbard: DS with $\kappa\ge1/4$ and $\|e^{sL}\rho-\sigma\|_1\le4Ne^{-s/4}$ on even states
-- statement:
--   Fix $D\ge1$, $\beta>0$ and finite bounds $t_*,\omega_*\ge0$. There exist an integer $\ell\ge1$ and $U_*>0$, depending only on $D,\beta,t_*,\omega_*$, with the following property. Let $\Lambda\subset\mathbb Z^D$ be finite, $N=|\Lambda|$, and let $H$ be the Fermi–Hubbard Hamiltonian (7.12) with
--   $$t_{\max}\le t_*,\qquad U_{\max}=\max_i|U_i|\le U_*,\qquad\omega_{\max}=\tfrac12\Bigl(\max_i(\mu_i+U_i/2)-\min_i(\mu_i+U_i/2)\Bigr)\le\omega_*.$$
--   With $T_0=2\log16$, the fermionic block channels $\Phi_B(H,T_0)$ of Section 7 on the labelled cubes of side $\ell$ satisfy the quantum DS condition with $\kappa\ge1/4$: they are parity-covariant channels with common fixed state $\sigma_{\beta,H}$ and fermionic DS constant at least $1/4$. For the sampler $L=\ell^{-D}\sum_B(\Phi_B(H,T_0)-\mathrm{id})$,
--   $$\|e^{sL}(\rho)-\sigma_{\beta,H}\|_1\le4Ne^{-s/4},\qquad s\ge0,\qquad(1.7)$$
--   for every even state $\rho$, and hence $t^{\mathrm{even}}_{\mathrm{mix}}(L,\varepsilon)\le4\log(4N/\varepsilon)$, the supremum being over even initial states.
--
--   The result gives logarithmic mixing for the Fermi–Hubbard model at every fixed hopping-to-temperature ratio, for sufficiently weak on-site interactions with bounded effective-potential spread.
--
--   **Formalization Note** $\ell$ and $U_*$ are chosen before $\Lambda$, the mode ordering and the couplings. The common Gibbs fixed point is asserted to be an even state. Parity covariance is $\Phi\circ\Theta=\Theta\circ\Phi$, and $t^{\mathrm{even}}_{\mathrm{mix}}$ is `tmixEven`.
--
--   Differences from the source:
--   - encoding: Fock space H_Λ of dimension 4^{|Λ|} with the CAR embedding and a fixed Majorana ordering → matrices on Fin M → Fin 2 (M = 2|Λ| modes) with Jordan–Wigner c from the published GaussTesting.annihilator, for every mode ordering ord : Λ × Fin 2 ≃ Fin M; reason: the same algebra; changing the ordering conjugates by a unitary and leaves every quantity invariant (p.64), so the statement for every ordering is the statement for the fixed one
--   - encoding: κ(H) = min_j Σ_B ℓ^{−D}[1 − D^F_{Φ_B}(j)] ≥ x → FermiKappaGe: Σ_B ℓ^{−D} D^F_{Φ_B}(j) ≤ Σ_B ℓ^{−D} − x in ℝ≥0∞ for every site j; reason: the same inequality, since Σ_B ℓ^{−D} ≥ 1 ≥ x (each site lies in ℓ^D cubes)
--   - encoding: finite Λ ⊂ ℤ^D → a nonempty Finset Λ; reason: excludes only the empty lattice, where the minimum over sites is undefined
--   - encoding: the block channels satisfy the quantum DS condition with κ ≥ 1/4 → σ_{β,H} = gibbs β H is an even state, each Φ_B(H, T0) is a channel, commutes with Θ and fixes σ_{β,H}, and FermiKappaGe … (1/4); reason: the components of the fermionic DS condition (7.11): parity-preserving channels with a common even fixed state and κ ≥ 1/4
--   - reading: t^even_mix(L, ε) ≤ 4 log(4N/ε) (ε unrestricted in the statement) → for every 0 < ε < 1; reason: mixing times are defined for 0 < ε < 1 as in (4.15)/(4.17); for ε ≥ 4N the right side is not positive and the literal claim would be false
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Theorem 1.1, p.6 (definitions §7 pp.62–66; DS condition (7.11) p.65)

import Mathlib
import Definitions.Def_QDSGibbs_Supplement_fermiBlockChannel
import Definitions.Def_QDSGibbs_Supplement_fermiInfluence

open scoped Matrix ENNReal

namespace QDSGibbs.Supplement

/-- **Theorem 1.1 (Weak interactions around a hopping Gaussian reference)** (Rouzé–Stilck França,
*Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions*, arXiv:2610.03578, held
file sha256 ede55815…, Theorem 1.1, p.6). Fix `D ≥ 1`, `β > 0` and finite bounds `t_*, ω_* ≥ 0`. There
exist an integer `ℓ ≥ 1` and `U_* > 0`, depending only on `D, β, t_*, ω_*`, such that for every finite
`Λ ⊂ ℤ^D` and every Fermi–Hubbard Hamiltonian (7.12) with `t_max ≤ t_*`, `U_max ≤ U_*`,
`ω_max ≤ ω_*`: with `T_0 = 2 log 16`, the fermionic block channels of Section 7 on the labelled cubes of
side `ℓ` satisfy the quantum DS condition with `κ ≥ 1/4`; for `L = ℓ^{−D} Σ_B (Φ_B(H, T_0) − id)` and
`N = |Λ|`, `‖e^{sL}(ρ) − σ_{β,H}‖₁ ≤ 4Ne^{−s/4}` for every `s ≥ 0` and every even state `ρ` (1.7); thus
`t^even_mix(L, ε) ≤ 4 log(4N/ε)`.

**Formalization Note**
* Quantifier order: `ℓ` and `U_*` are chosen after `D, β, t_*, ω_*` and before `Λ`, the mode ordering
  `ord` and the couplings `t, U, μ`.
* The DS condition (7.11) consists of: channels (CPTP), parity covariant (`Φ ∘ Θ = Θ ∘ Φ`), with the
  common even fixed state `σ_{β,H} = gibbs β H`, and `κ ≥ 1/4` (`FermiKappaGe` with rate `ℓ^{−D}`).
* The mixing-time clause is stated for `0 < ε < 1`, the range of (4.15)/(4.17) (for `ε ≥ 4N` the
  right side `4 log(4N/ε)` is not positive). `t^even_mix` is `tmixEven` (supremum over even states).
* `Λ` is a nonempty `Finset` (`N = Λ.card ≥ 1`); `e^{sL}` is the base `sexp`. -/
theorem theorem_1_1 :
    ∀ (D : ℕ), 1 ≤ D → ∀ (β tstar ωstar : ℝ), 0 < β → 0 ≤ tstar → 0 ≤ ωstar →
      ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ∃ Ustar : ℝ, 0 < Ustar ∧
        ∀ (Λ : Finset (Fin D → ℤ)), Λ.Nonempty → ∀ (M : ℕ) (ord : Λ × Fin 2 ≃ Fin M)
          (t : Sym2 Λ → ℝ) (U μ : Λ → ℝ),
          tMaxL Λ t ≤ tstar → uMax U ≤ Ustar → omegaMax U μ ≤ ωstar →
          IsState (gibbs β (fhLattice Λ ord t U μ).ham) ∧
          FermiHubbardMix.IsEven (gibbs β (fhLattice Λ ord t U μ).ham) ∧
          (∀ z ∈ cubeLabels Λ ℓ,
            IsChannel (fermiBlockChannel β ord (fhLattice Λ ord t U μ) (cube Λ ℓ z) (2 * Real.log 16)) ∧
            fermiBlockChannel β ord (fhLattice Λ ord t U μ) (cube Λ ℓ z) (2 * Real.log 16)
                (gibbs β (fhLattice Λ ord t U μ).ham) = gibbs β (fhLattice Λ ord t U μ).ham ∧
            ∀ X, fermiBlockChannel β ord (fhLattice Λ ord t U μ) (cube Λ ℓ z) (2 * Real.log 16)
                (parityConj X) =
              parityConj (fermiBlockChannel β ord (fhLattice Λ ord t U μ) (cube Λ ℓ z)
                (2 * Real.log 16) X)) ∧
          FermiKappaGe ord (cubeLabels Λ ℓ)
            (fun z => fermiBlockChannel β ord (fhLattice Λ ord t U μ) (cube Λ ℓ z) (2 * Real.log 16))
            (((ℓ : ℝ) ^ D)⁻¹) (1 / 4) ∧
          (∀ ρ : FermiHubbardMix.Op M, IsState ρ → FermiHubbardMix.IsEven ρ → ∀ s : ℝ, 0 ≤ s →
            traceNorm (sexp (fermiSampler Λ β ord (fhLattice Λ ord t U μ) ℓ (2 * Real.log 16)) s ρ -
                gibbs β (fhLattice Λ ord t U μ).ham) ≤
              4 * (Λ.card : ℝ) * Real.exp (-s / 4)) ∧
          ∀ ε : ℝ, 0 < ε → ε < 1 →
            tmixEven (fermiSampler Λ β ord (fhLattice Λ ord t U μ) ℓ (2 * Real.log 16))
                (gibbs β (fhLattice Λ ord t U μ).ham) ε ≤
              ENNReal.ofReal (4 * Real.log (4 * (Λ.card : ℝ) / ε)) := by sorry

end QDSGibbs.Supplement
