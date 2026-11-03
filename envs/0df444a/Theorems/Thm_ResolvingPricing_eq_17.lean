-- Prove2me | Theorems.Thm_ResolvingPricing_eq_17
-- name    : ResolvingPricing.eq_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:26:42.002517+00:00
-- url     : https://prove2.me/theorems/b4a1be0e-dd03-44f6-8e8c-36208c75e5ec
-- title:
--   Eq. (17): a summation identity behind $\mathbb E[\mathcal A]$
-- statement:
--   Let $T\ge0$, let $s$ be an integer with $2\le s\le T+1$ (standing for $T^\sharp$), and let $(\Delta_\tau)$, $(\xi^\delta_\tau)$ be real sequences with harmonic series $\bar\Delta_{\to\tau}$, $\bar\xi^\delta_{\to\tau}$. Then
--   $$\sum_{\tau=s}^{T}\big[\Delta_\tau-\bar\Delta_{\to\tau}+\bar\xi^\delta_{\to\tau}-\xi^\delta_\tau\big]-(s-1)\big(\bar\Delta_{\to s-1}-\bar\xi^\delta_{\to s-1}\big)=0.$$
--
--   In the proof of Theorem 3 this identity collapses the term $\mathcal A$ of the regret decomposition (16) to $\mathbb E[(T^\sharp-1)\eta]$.
--
--   Differences from the source:
--   - generalization: Δ_τ, ξ^δ_τ of the optimal and resolving policies and the random time T♯ → arbitrary real sequences and an arbitrary integer s; reason: the identity is deterministic ("elementary algebra"); the paper's quantities are particular values
--   - encoding: the identity at every value of T♯ → 2 ≤ s ≤ T + 1; reason: at T♯ = 1 the printed term Δ̄→0 contains Δ_1/0
-- source:
--   Y. Wang, H. Wang, Constant Regret Resolving Heuristics for Price-Based Revenue Management, Oper. Res. 70(6):3538–3557 (2022), doi:10.1287/opre.2021.2219, §4.2, Eq. (17), p.3545 (PDF p.9)

import Mathlib
import Definitions.Def_ResolvingPricing_Run

open MeasureTheory

namespace ResolvingPricing

/-- **Eq. (17)**, Y. Wang, H. Wang, *Constant Regret Resolving Heuristics for Price-Based Revenue Management*,
Oper. Res. 70(6) (2022), p.3545: "with elementary algebra, it can be verified that
∑_{τ=T♯}^T [Δ_τ − Δ̄→τ + ξ̄^δ→τ − ξ^δ_τ] − (T♯ − 1)(Δ̄→T♯−1 − ξ̄^δ→T♯−1) = 0".

For all real sequences `Δ`, `ξ^δ` indexed by periods and every integer `2 ≤ T♯ ≤ T + 1`.

**Formalization Note.** The identity is deterministic and is stated for arbitrary sequences and an
arbitrary integer in place of `T♯`. It is stated for `T♯ ≥ 2`: at `T♯ = 1` the printed term
`Δ̄→0` contains `Δ_1/0`. -/
theorem eq_17 (T s : ℕ) (hs : 2 ≤ s) (hsT : s ≤ T + 1) (Δ ξδ : ℕ → ℝ) :
    ∑ τ ∈ Finset.Icc s T, (Δ τ - harm T Δ τ + harm T ξδ τ - ξδ τ)
      - ((s : ℝ) - 1) * (harm T Δ (s - 1) - harm T ξδ (s - 1)) = 0 := by sorry

end ResolvingPricing
