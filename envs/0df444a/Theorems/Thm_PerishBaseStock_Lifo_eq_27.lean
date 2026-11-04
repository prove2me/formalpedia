-- Prove2me | Theorems.Thm_PerishBaseStock_Lifo_eq_27
-- name    : PerishBaseStock.Lifo.eq_27
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:13.744697+00:00
-- url     : https://prove2.me/theorems/eccf2638-33e1-4e5b-aac2-6fa897c2b22c
-- title:
--   (27) — the optimality gap of $\pi_{\hat S}$ in terms of $\hat S$ and $\widetilde S$
-- statement:
--   In the LIFO perishable inventory system with lifetime $m\ge 1$ and costs $h>0$, $p>0$, $\theta\ge 0$, let $\hat S$ minimize $(\hat C_L+\hat C_U)/2$ and $\widetilde S$ minimize $\widetilde C$ over $[0,\infty)$. Then
--   $$C^{LIFO}(\hat S)-\mathrm{OPT}^{LIFO}\le\frac{\theta}{2m}\Big(\mathbb E[(\hat S-D)^+]+\mathbb E[(\widetilde S-D)^+]-\mathbb E[(\hat S-\max\{D_1,\dots,D_m\})^+]+\mathbb E[(\widetilde S-\max\{D_1,\dots,D_m\})^+]-2\mathbb E\Big[\Big(\widetilde S-\sum_{i=1}^mD_i\Big)^+\Big]\Big).$$
--
--   Parts (a) and (b) of Theorem 5 are read off this bound.
--
--   **Formalization Note** The gap is stated as $C^{LIFO}(\hat S)\le\mathrm{OPT}^{LIFO}+B$ in $[0,\infty]$, which is equivalent because $\mathrm{OPT}^{LIFO}$ is finite. The bound holds for every pair of minimizers.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 24, §6.2, (27)

import Definitions.Def_PerishBaseStock_Lifo_Heuristic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace PerishBaseStock.Lifo

/-- (27): the gap of `π_Ŝ` in terms of `Ŝ` and `S̃`, for every pair of minimizers. -/
theorem eq_27 (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing)
    (Sh St : ℝ≥0) (hSh : IsHatMinimizer P c Sh) (hSt : IsTildeMinimizer P c St) :
    baseStockCost P c Sh ≤ OPT P c + ENNReal.ofReal (c.θ / (2 * c.m) *
      (expectedHolding P.law Sh + expectedHolding P.law St
        - expectedHolding (maxLaw P (c.m - 1)) Sh + expectedHolding (maxLaw P (c.m - 1)) St
        - 2 * expectedHolding (leadTimeLaw P (c.m - 1)) St)) := by sorry

end PerishBaseStock.Lifo
