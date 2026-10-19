-- Prove2me | Theorems.Thm_QuantumMC_Cooling_chiSq_gibbs_eq
-- name    : QuantumMC.Cooling.chiSq_gibbs_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:27:00.167742+00:00
-- url     : https://prove2.me/theorems/d4cb6485-f923-4ae3-a7df-c8911d055944
-- title:
--   Display (1), §3.2, p. 16 — χ²(π_{i+1}, π_i) = Z(β_i)Z(2β_{i+1} − β_i)/Z(β_{i+1})² − 1
-- statement:
--   Let $\Omega$ be finite, $H:\Omega\to\mathbb N$ a Hamiltonian with at least one configuration of energy $0$, and $0=\beta_0<\beta_1<\dots<\beta_\ell=\infty$ a cooling schedule, with Gibbs distributions $\pi_i(x)=e^{-\beta_iH(x)}/Z(\beta_i)$. Then for every $i\in\{0,\dots,\ell-1\}$,
--   $$\chi^2(\pi_{i+1},\pi_i)=\frac{Z(\beta_i)\,Z(2\beta_{i+1}-\beta_i)}{Z(\beta_{i+1})^2}-1.$$
--
--   The identity includes the last step $i=\ell-1$, where $\beta_{i+1}=\infty$ and $2\beta_{i+1}-\beta_i=\infty$. It shows that the Chebyshev cooling condition of Definition 1 is exactly a bound on $\chi^2(\pi_{i+1},\pi_i)+1$.
--
--   **Formalization Note** The hypothesis that some $x$ has $H(x)=0$ makes $Z(\infty)>0$, without which $\pi_\ell$ is undefined; it is added and disclosed. The bound $H\le n$ of the paper's model is not needed for this identity and is omitted.
-- source:
--   Montanaro, Quantum speedup of Monte Carlo methods, arXiv:1504.06987v3, §3.2, display (1), p. 16

import Mathlib
import Definitions.Def_QuantumMC_Cooling_Setting

open scoped ENNReal InnerProductSpace

namespace QuantumMC.Cooling

/-- §3.2, display (1), p. 16: along a cooling schedule `0 = β_0 < ⋯ < β_ℓ = ∞`, for every
`i < ℓ` (including `β_{i+1} = ∞`),
`χ²(π_{i+1}, π_i) = Z(β_i) Z(2β_{i+1} - β_i) / Z(β_{i+1})² - 1`. -/
theorem chiSq_gibbs_eq {Ω : Type*} [Fintype Ω] (H : Ω → ℕ) (hZ : ∃ x, H x = 0)
    (β : ℕ → ℝ≥0∞) (ℓ : ℕ) (hβ : IsCoolingSchedule β ℓ) (i : ℕ) (hi : i < ℓ) :
    chiSq (gibbs H (β (i + 1))) (gibbs H (β i)) =
      Z H (β i) * Z H (2 * β (i + 1) - β i) / Z H (β (i + 1)) ^ 2 - 1 := by sorry

end QuantumMC.Cooling
