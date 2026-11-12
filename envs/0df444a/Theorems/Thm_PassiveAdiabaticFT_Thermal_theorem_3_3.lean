-- Prove2me | Theorems.Thm_PassiveAdiabaticFT_Thermal_theorem_3_3
-- name    : PassiveAdiabaticFT.Thermal.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:52.183+00:00
-- url     : https://prove2.me/theorems/4362d30f-4e71-4af6-865f-9071eb3bf104
-- title:
--   Theorem 3.3 — noisy dressed path versus the ideal logical evolution (diamond norm)
-- statement:
--   Let $K(t)$ be any Hermitian logical Hamiltonian path on $N$ blocks of a stabilizer code with a Pauli decoder and penalty $J>0$, $H(t)=\sum_iH_0^{(i)}+\hat K(t)$, $\mathcal L_\beta(t)$ the generator (3.3) with rates satisfying (1.18)–(1.19) at bath inverse temperature $\beta$, $\Phi_t$ its evolution and $\mathcal U_t$ the ideal logical evolution $U_t=\mathcal T\exp(-i\int_0^tK)$. For every $t\ge0$ and every $\beta'\ge\beta$,
--   $$\big\|\mathrm{Dec}\circ\Phi_t\circ\mathrm{Enc}_{\beta'}-\mathcal U_t\big\|_\diamond\le2t(\gamma+\kappa)\frac{Z_1(\beta)}{Z_1(\beta')}\sum_{\alpha,i}\pi_\beta(D_\alpha^{(i)}),\qquad(3.27)$$
--   and for the code-space encoding the same bound holds with $Z_1(\beta')$ replaced by $2^k$ (p. 25). Here the diamond norm is evaluated as stated: for every finite reference register $R$ and joint state $\sigma_{Q,R}$, the trace norm of $(\mathrm{Dec}\otimes\mathcal I_R)(\rho(t))-(U_t\otimes I)\sigma_{Q,R}(U_t\otimes I)^\dagger$, where $\rho$ solves $\dot\rho=(\mathcal L_\beta(u)\otimes\mathcal I_R)\rho$ from $(\mathrm{Enc}_{\beta'}\otimes\mathcal I_R)\sigma_{Q,R}$; $Z_1$ is the one-block partition function and $\pi_\beta(D_\alpha^{(i)})$ the product-Gibbs weight.
--
--   This is the paper's central error bound: the whole noisy computation is controlled by the Gibbs weight of dangerous syndromes.
--
--   Differences from the source:
--   - encoding: ‖·‖₁ → QAlgorithms.traceNorm M = Re Tr √(M†M); reason: the trace norm, unhalved as printed
--   - encoding: the diamond norm ‖·‖_⋄ → for every finite reference type R and every joint state σ (PSD, trace 1), the trace-norm bound; reason: the diamond norm is the supremum of exactly these quantities
--   - encoding: Φ_t = T exp ∫ L_β and U_t = T exp(−i∫K) → every solution in the IsSolution sense (continuous, derivative off a countable set) from the encoded state, and every propagator U; reason: the time-ordered exponentials are these solutions; the exceptional set admits generators that jump at level crossings
--   - generalization: Theorem 3.3 states β′ ≥ β → also the code-space encoding, with Z_1(β′) replaced by 2^k; reason: the source states this clause after the proof (p. 25); the thermal clause is unchanged
-- source:
--   Arsalan Motamedi, Peter Love, Fault Tolerant Adiabatic Quantum Computation from Passive Error Correcting Codes, STOC 2027 submission #1144 (October 2026), source.pdf SHA-256 96d4a748a9114e6a9ed0c5252e84434a63b2a1ef07b286134f01f6761c2503b8, p. 23, Theorem 3.3 (3.27) (proof pp. 23–25), and the ground-state clause at the end of the proof, p. 25

import Mathlib
import Definitions.Def_PassiveAdiabaticFT_Thermal_Blocks

set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix ComplexOrder

namespace PassiveAdiabaticFT.Thermal

/-- Theorem 3.3 (p. 23), in its diamond-norm form (for every reference register and joint
state) together with the ground-state clause of p. 25: for any `β' ≥ β`,
`‖Dec ∘ Φ_t ∘ Enc_{β'} − 𝒰_t‖_⋄ ≤ 2t(γ + κ) (Z_1(β)/Z_1(β')) Σ_{α,i} π_β(D_α^{(i)})` (3.27), and
with the code-space encoding the same bound holds with `Z_1(β')` replaced by `2^k`. -/
theorem theorem_3_3 {b : ℕ} (C : StabCode b) (D : PauliDecoder C) (N : ℕ) (J : ℝ) (hJ : 0 < J)
    (β γ κ : ℝ) (γr κr : Fin N × (Fin b × Fin 3) → ℝ → ℝ) (hrates : RatesAdmissible β γ κ γr κr)
    (K : ℝ → Op (Fin N × Fin C.k)) (hK : ∀ u, (K u).IsHermitian) (t : ℝ) (ht : 0 ≤ t)
    {R : Type} [Fintype R] [DecidableEq R]
    (σ : Matrix ((Fin N × Fin C.k → Fin 2) × R) ((Fin N × Fin C.k → Fin 2) × R) ℂ)
    (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (U : ℝ → Op (Fin N × Fin C.k)) (hU : IsPropagator K t U) :
    (∀ β' : ℝ, β ≤ β' →
      ∀ ρ : ℝ → Matrix ((Fin N × Fin b → Fin 2) × R) ((Fin N × Fin b → Fin 2) × R) ℂ,
        ρ 0 = D.encThNRef N J β' σ →
        IsSolution (fun u => D.noisyGenRef N J γr κr (K u)) t ρ →
        QAlgorithms.traceNorm
            (D.decNRef N (ρ t) - liftRef (R := R) (U t) * σ * (liftRef (R := R) (U t))ᴴ) ≤
          2 * t * (γ + κ) * (C.Z J β / C.Z J β') *
            ∑ i, ∑ α, C.massN N (C.gibbsN N J β) (D.DsetN N i α)) ∧
    (∀ ρ : ℝ → Matrix ((Fin N × Fin b → Fin 2) × R) ((Fin N × Fin b → Fin 2) × R) ℂ,
        ρ 0 = C.encCodeNRef N σ →
        IsSolution (fun u => D.noisyGenRef N J γr κr (K u)) t ρ →
        QAlgorithms.traceNorm
            (D.decNRef N (ρ t) - liftRef (R := R) (U t) * σ * (liftRef (R := R) (U t))ᴴ) ≤
          2 * t * (γ + κ) * (C.Z J β / 2 ^ C.k) *
            ∑ i, ∑ α, C.massN N (C.gibbsN N J β) (D.DsetN N i α)) := by sorry

end PassiveAdiabaticFT.Thermal
