-- Prove2me | Theorems.Thm_QDSGibbs_Supplement_theorem_7_3
-- name    : QDSGibbs.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:30:06.70172+00:00
-- url     : https://prove2.me/theorems/b857c454-04ea-43a8-b568-f01ec324f4a1
-- title:
--   Theorem 7.3 — weak interactions around a Gaussian reference: explicit bound (7.19) on $\kappa(H)$, and $\kappa(H)\ge1/4$
-- statement:
--   Let $D\ge1$. For a finite $\Lambda\subset\mathbb Z^D$ and the Fermi–Hubbard Hamiltonian $H$ (7.12), consider the fermionic block channels $\Phi_B(H,T)=e^{T\mathcal K_B}$ (7.18) on all nonempty labelled cubes of side $\ell$, with rates $\ell^{-D}$, and their fermionic DS constant $\kappa(H)$ (7.11). For every $\beta>0$, $T\ge0$ and integer $\ell\ge1$ satisfying
--   $$\beta U_{\max}(\ell+2)^{8D^2+10D-2}(1+\beta t_{\max})^{16D+2}e^{8D\beta t_{\max}}\le\frac{1}{9\cdot2^{176D+46}D^{32D+2}},\qquad(7.20)$$
--   one has
--   $$\begin{aligned}\kappa(H)\ge{}&1-4e^{-T/2}-\frac{T}{5\ell}[32D(1+2D\beta t_{\max})]^{16D^2}(1+\beta\omega_{\max})^{3D+1}e^{(6D^2+2D)\beta t_{\max}+T}\\&-2^{72D+20}D^{12D+1}T(\ell+2)^{4D^2+5D-1}(1+\beta t_{\max})^{8D+1}e^{4D\beta t_{\max}}\,\beta U_{\max}\Bigl[1+\log\frac{4}{\beta U_{\max}}\Bigr]^{4D},\end{aligned}\qquad(7.19)$$
--   where the last factor is $0$ at $U_{\max}=0$.
--
--   In particular, fix $\beta>0$ and finite bounds $t_*,\omega_*\ge0$, set $T_0=2\log16$, let $\ell\ge1$ be an integer with
--   $$\ell\ge\frac{4T_0}{5}[32D(1+2D\beta t_*)]^{16D^2}(1+\beta\omega_*)^{3D+1}e^{(6D^2+2D)\beta t_*+T_0},\qquad(7.21)$$
--   and let $U_*>0$ satisfy (7.20) with $t_{\max}=t_*$, $U_{\max}=U_*$. Then $\kappa(H)\ge1/4$ for the channels at time $T_0$ whenever $t_{\max}\le t_*$, $\omega_{\max}\le\omega_*$ and $U_{\max}\le U_*$.
--
--   The three losses in (7.19) are the bulk relaxation, the Gaussian boundary contribution and the interaction perturbation; at $U_{\max}=0$ the bound holds at every finite temperature.
--
--   **Formalization Note** The fermionic influence and transport norm are those of (7.10) and (7.7), built on the published Bakshi–Moitra–Tan fermionic partial trace and transport plans. $t_{\max}$, $U_{\max}$, $\omega_{\max}$ are `tMaxL`, `uMax`, `omegaMax`, and the $U_{\max}=0$ convention is `uLoss`.
--
--   Differences from the source:
--   - encoding: Fock space H_Λ of dimension 4^{|Λ|} with the CAR embedding and a fixed Majorana ordering → matrices on Fin M → Fin 2 (M = 2|Λ| modes) with Jordan–Wigner c from the published GaussTesting.annihilator, for every mode ordering ord : Λ × Fin 2 ≃ Fin M; reason: the same algebra; changing the ordering conjugates by a unitary and leaves every quantity invariant (p.64), so the statement for every ordering is the statement for the fixed one
--   - encoding: κ(H) = min_j Σ_B ℓ^{−D}[1 − D^F_{Φ_B}(j)] ≥ x → FermiKappaGe: Σ_B ℓ^{−D} D^F_{Φ_B}(j) ≤ Σ_B ℓ^{−D} − x in ℝ≥0∞ for every site j; reason: the same inequality, since Σ_B ℓ^{−D} ≥ 1 ≥ x (each site lies in ℓ^D cubes)
--   - encoding: finite Λ ⊂ ℤ^D → a nonempty Finset Λ; reason: excludes only the empty lattice, where the minimum over sites is undefined
--   - encoding: βU_max[1 + log(4/(βU_max))]^{4D}, interpreted as 0 at U_max = 0 → uLoss D (β·U_max), defined by cases (0 at argument 0); reason: the source's convention, avoiding Lean's log 0 = 0
--   - reading: first set T0, then choose ℓ with (7.21), finally choose U* > 0 so that (7.20) holds at t_max = t*, U_max = U* → for every integer ℓ ≥ 1 satisfying (7.21) and every U* > 0 satisfying (7.20) at (t*, U*); reason: the source's choices are arbitrary among those satisfying the stated conditions, so the conclusion is claimed for each of them
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Theorem 7.3, p.67 (definitions §7 pp.62–66: (7.4), (7.7), (7.10)–(7.12), (7.14)–(7.18))

import Mathlib
import Definitions.Def_QDSGibbs_Supplement_fermiBlockChannel
import Definitions.Def_QDSGibbs_Supplement_fermiInfluence

open scoped Matrix ENNReal

namespace QDSGibbs.Supplement

/-- **Theorem 7.3 (Weak interactions around a Gaussian reference)** (Rouzé–Stilck França, *Rapid
mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions*, arXiv:2610.03578, held file
sha256 ede55815…, Theorem 7.3, p.67). For every `D ≥ 1`, the fermionic block channels (7.18) of the
Fermi–Hubbard Hamiltonian (7.12) on the labelled cubes of side `ℓ` with rates `ℓ^{−D}` satisfy
`κ(H) ≥ 1 − 4e^{−T/2} − (T/(5ℓ)) [32D(1 + 2Dβt_max)]^{16D²} (1 + βω_max)^{3D+1} e^{(6D²+2D)βt_max+T}
− 2^{72D+20} D^{12D+1} T (ℓ+2)^{4D²+5D−1} (1 + βt_max)^{8D+1} e^{4Dβt_max} · βU_max [1 + log(4/(βU_max))]^{4D}`
(7.19) for every `β > 0`, `T ≥ 0` and integer `ℓ ≥ 1` satisfying
`βU_max (ℓ+2)^{8D²+10D−2} (1 + βt_max)^{16D+2} e^{8Dβt_max} ≤ 1/(9 · 2^{176D+46} D^{32D+2})` (7.20), the
`U_max`-factor being `0` at `U_max = 0`. In particular, for finite bounds `t_*`, `ω_*`, with
`T_0 = 2 log 16`, every integer `ℓ ≥ 1` satisfying (7.21) and every `U_* > 0` satisfying (7.20) with
`t_max = t_*`, `U_max = U_*` give `κ(H) ≥ 1/4` whenever `t_max ≤ t_*`, `ω_max ≤ ω_*`, `U_max ≤ U_*`.

**Formalization Note**
* The lattice `Λ ⊂ ℤ^D` is a nonempty `Finset`; `ord : Λ × Fin 2 ≃ Fin M` is the Jordan–Wigner mode
  ordering (any ordering); `H = fhLattice Λ ord t U μ` (the published `FermiHubbardMix.fhHam` on the
  nearest-neighbour graph). The blocks are all nonempty cubes `cube Λ ℓ z`, `z ∈ cubeLabels Λ ℓ`.
* `κ(H) ≥ x` is `FermiKappaGe` with rate `ℓ^{−D}` (no subtraction under the sum; see its docstring),
  using the fermionic influence (7.10) and transport norm (7.7).
* The `U_max = 0` convention is `uLoss`. `t_max`, `U_max`, `ω_max` are `tMaxL`, `uMax`, `omegaMax`. -/
theorem theorem_7_3 (D : ℕ) (hD : 1 ≤ D) :
    (∀ (Λ : Finset (Fin D → ℤ)), Λ.Nonempty → ∀ (M : ℕ) (ord : Λ × Fin 2 ≃ Fin M)
      (t : Sym2 Λ → ℝ) (U μ : Λ → ℝ) (β T : ℝ) (ℓ : ℕ), 0 < β → 0 ≤ T → 1 ≤ ℓ →
      β * uMax U * ((ℓ : ℝ) + 2) ^ (8 * D ^ 2 + 10 * D - 2) *
          (1 + β * tMaxL Λ t) ^ (16 * D + 2) * Real.exp (8 * (D : ℝ) * β * tMaxL Λ t) ≤
        1 / (9 * (2 : ℝ) ^ (176 * D + 46) * (D : ℝ) ^ (32 * D + 2)) →
      FermiKappaGe ord (cubeLabels Λ ℓ)
        (fun z => fermiBlockChannel β ord (fhLattice Λ ord t U μ) (cube Λ ℓ z) T)
        (((ℓ : ℝ) ^ D)⁻¹)
        (1 - 4 * Real.exp (-T / 2)
          - T / (5 * (ℓ : ℝ)) * (32 * (D : ℝ) * (1 + 2 * (D : ℝ) * β * tMaxL Λ t)) ^ (16 * D ^ 2) *
              (1 + β * omegaMax U μ) ^ (3 * D + 1) *
              Real.exp ((6 * (D : ℝ) ^ 2 + 2 * (D : ℝ)) * β * tMaxL Λ t + T)
          - (2 : ℝ) ^ (72 * D + 20) * (D : ℝ) ^ (12 * D + 1) * T * ((ℓ : ℝ) + 2) ^ (4 * D ^ 2 + 5 * D - 1) *
              (1 + β * tMaxL Λ t) ^ (8 * D + 1) * Real.exp (4 * (D : ℝ) * β * tMaxL Λ t) *
              uLoss D (β * uMax U))) ∧
    (∀ (β tstar ωstar : ℝ), 0 < β → 0 ≤ tstar → 0 ≤ ωstar →
      ∀ ℓ : ℕ, 1 ≤ ℓ →
        4 * (2 * Real.log 16) / 5 * (32 * (D : ℝ) * (1 + 2 * (D : ℝ) * β * tstar)) ^ (16 * D ^ 2) *
            (1 + β * ωstar) ^ (3 * D + 1) *
            Real.exp ((6 * (D : ℝ) ^ 2 + 2 * (D : ℝ)) * β * tstar + 2 * Real.log 16) ≤ (ℓ : ℝ) →
      ∀ Ustar : ℝ, 0 < Ustar →
        β * Ustar * ((ℓ : ℝ) + 2) ^ (8 * D ^ 2 + 10 * D - 2) * (1 + β * tstar) ^ (16 * D + 2) *
            Real.exp (8 * (D : ℝ) * β * tstar) ≤
          1 / (9 * (2 : ℝ) ^ (176 * D + 46) * (D : ℝ) ^ (32 * D + 2)) →
      ∀ (Λ : Finset (Fin D → ℤ)), Λ.Nonempty → ∀ (M : ℕ) (ord : Λ × Fin 2 ≃ Fin M)
        (t : Sym2 Λ → ℝ) (U μ : Λ → ℝ),
        tMaxL Λ t ≤ tstar → omegaMax U μ ≤ ωstar → uMax U ≤ Ustar →
        FermiKappaGe ord (cubeLabels Λ ℓ)
          (fun z => fermiBlockChannel β ord (fhLattice Λ ord t U μ) (cube Λ ℓ z) (2 * Real.log 16))
          (((ℓ : ℝ) ^ D)⁻¹) (1 / 4)) := by sorry

end QDSGibbs.Supplement
