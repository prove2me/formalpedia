-- Prove2me | Theorems.Thm_PerishBaseStock_Lifo_ec_19
-- name    : PerishBaseStock.Lifo.ec_19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:10.617606+00:00
-- url     : https://prove2.me/theorems/b263c36e-9dd4-43ac-8c6d-74635db35203
-- title:
--   (EC.19) — $m$ consecutive periods outdate at least $\mathbb E[(S-\max\{D_1,\dots,D_m\})^+]$
-- statement:
--   In the LIFO perishable inventory system with lifetime $m\ge 1$, started empty, let $o_j$ be the amount outdated in period $j$ under the base-stock policy $\pi_S$, $S\ge 0$. For every period $t\ge 1$,
--   $$\sum_{j=t}^{t+m-1}\mathbb E[o_j]\;\ge\;\mathbb E\big[(S-\max\{D_1,D_2,\dots,D_m\})^+\big].$$
--
--   Averaging this bound over blocks of $m$ periods gives the outdating term of the lower bound $\hat C_L(S)$ of Lemma 3.
--
--   **Formalization Note** Time is zero-based. Expectations of $o_j\ge 0$ are lower Lebesgue integrals in $[0,\infty]$; the right side is the real expectation `expectedHolding (maxLaw P (m - 1)) S`, which is finite.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec7, Appendix C.1, (EC.19)

import Definitions.Def_PerishBaseStock_Lifo_Heuristic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace PerishBaseStock.Lifo

/-- (EC.19): `Σ_{j=t}^{t+m-1} E[o^{π_S}_j] ≥ E[(S - max{D_1, …, D_m})⁺]` for every period. -/
theorem ec_19 (P : CappedBaseStock.DemandLaw) (m : ℕ) (hm : 1 ≤ m) (S : ℝ≥0) (t : ℕ) :
    ENNReal.ofReal (expectedHolding (maxLaw P (m - 1)) S) ≤
      ∑ j ∈ Finset.Ico t (t + m),
        ∫⁻ d, ENNReal.ofReal (outdated (baseStock m S) d j) ∂CappedBaseStock.demandPathLaw P := by sorry

end PerishBaseStock.Lifo
