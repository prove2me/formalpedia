-- Prove2me | Theorems.Thm_PrimalDualPricing_Regret_proposition_2
-- name    : PrimalDualPricing.Regret.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:26:52.161024+00:00
-- url     : https://prove2.me/theorems/3870ecde-86b7-45c1-b2d0-786cecb6bc6f
-- title:
--   Proposition 2, p. 15 — when $z^*=0$, $R^\pi_n(T,c)=O((\log n)^{2+16\epsilon}n^{-1/2})$
-- statement:
--   Under Assumptions 1–2 and Remark 2, with $M\ge1$ consumer types, suppose $z^*=0$ (sufficient capacity). For every sufficiently small $\epsilon>0$ there is a constant $C$, independent of $n$, such that the regret of Algorithm 1 with parameter $\epsilon$ satisfies, for every $n\ge3$,
--   $$R^\pi_n(T,c)=1-\frac{J^\pi_n(T,c)}{J^D_n(T,c)}\le C(\log n)^{2+16\epsilon}n^{-1/2}.$$
--   The constant does not depend on the probability space carrying the independent unit-rate Poisson arrivals.
--
--   This is the sufficient-capacity case of Theorem 1.
--
--   **Formalization Note** The page writes "when $z^*\le0$"; since $z^*\ge0$, this means $z^*=0$. The formalized part is the regret conclusion, which concerns the real system: inventory $\lfloor nc\rfloor$, no sales after the stock-out. The intermediate bound on $J^D_n-\mathbb E[\tilde J^\pi_n]$ for the modified system is not stated. The page's comparison $\tilde J^\pi_n\le J^\pi_n$ (pp. 13–14) can fail as printed when a last-phase price exceeds $\overline p$. $M\ge1$ is the paper's standing setting: with no types $J^D_n=0$ and the regret is not meaningful.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, p. 15, §4.1, Proposition 2

import Mathlib
import Definitions.Def_PrimalDualPricing_Regret_System

namespace PrimalDualPricing.Regret

open MeasureTheory ProbabilityTheory

/-- Proposition 2 (Chen–Gallego, arXiv:1812.09234v3, p. 15), the regret part: when `z* ≤ 0` (that is,
`z* = 0`, sufficient capacity), `R^π_n(T, c) = O((log n)^{2+16ε} n^{−1/2})`. Under Assumptions 1–2 and
Remark 2 with `M ≥ 1` types and `z* = 0`, for every sufficiently small `ε > 0` there is `C`, independent of
`n`, such that for `M` independent unit-rate Poisson paths on any probability space and every `n ≥ 3`, the
regret of Algorithm 1 with parameter `ε` is at most `C (log n)^{2+16ε} n^{−1/2}`. -/
theorem proposition_2 {M : ℕ} (hM : 0 < M) (S : Setting M) (hz : S.zstar = 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₀ → ∃ C : ℝ,
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (N : Fin M → ℝ → Ω → ℕ), IndepPoissonPaths N →
        ∀ n : ℕ, 3 ≤ n →
          S.regret eps n N ≤ C * Real.log n ^ (2 + 16 * eps) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by sorry

end PrimalDualPricing.Regret
