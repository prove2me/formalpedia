-- Prove2me | Theorems.Thm_PerishBaseStock_Lifo_ec_20
-- name    : PerishBaseStock.Lifo.ec_20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:13.79845+00:00
-- url     : https://prove2.me/theorems/7ca3577e-0290-4bbc-9048-9f9000141ced
-- title:
--   (EC.20) — $C^{LIFO}(\hat S)-\mathrm{OPT}^{LIFO}\le(m-1)\theta\mathbb E[D]/m$
-- statement:
--   In the LIFO perishable inventory system with lifetime $m\ge 1$ and costs $h>0$, $p>0$, $\theta\ge 0$, let $\hat S$ minimize $(\hat C_L+\hat C_U)/2$ and $\widetilde S$ minimize $\widetilde C$ over $[0,\infty)$, and write $M=\max\{D_1,\dots,D_m\}$. Then
--   $$C^{LIFO}(\hat S)-\mathrm{OPT}^{LIFO}\le\frac{\theta}{2m}\Big(2(m-1)\mathbb E[D]+\mathbb E[(D-\hat S)^+]+\mathbb E[(D-\widetilde S)^+]-\mathbb E[(M-\hat S)^+]+\mathbb E[(M-\widetilde S)^+]-2\mathbb E\Big[\Big(\sum_{i=1}^mD_i-\widetilde S\Big)^+\Big]\Big)\le\frac{(m-1)\theta}{m}\mathbb E[D].$$
--
--   The bound is uniform in the penalty cost $p$; with $\mathrm{OPT}^{LIFO}_p\to\infty$ it gives part (b) of Theorem 5.
--
--   **Formalization Note** Both inequalities of the display are formalized, as a conjunction; the first is in $[0,\infty]$ as $C^{LIFO}(\hat S)\le\mathrm{OPT}^{LIFO}+B$, the second between real numbers.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. ec8, Appendix C.2, (EC.20)

import Definitions.Def_PerishBaseStock_Lifo_Heuristic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace PerishBaseStock.Lifo

/-- (EC.20): both inequalities of the display, for every pair of minimizers `Ŝ`, `S̃`. -/
theorem ec_20 (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing)
    (Sh St : ℝ≥0) (hSh : IsHatMinimizer P c Sh) (hSt : IsTildeMinimizer P c St) :
    baseStockCost P c Sh ≤ OPT P c + ENNReal.ofReal (c.θ / (2 * c.m) *
        (2 * ((c.m : ℝ) - 1) * CappedBaseStock.mean P + expectedShortfall P.law Sh
          + expectedShortfall P.law St - expectedShortfall (maxLaw P (c.m - 1)) Sh
          + expectedShortfall (maxLaw P (c.m - 1)) St
          - 2 * expectedShortfall (leadTimeLaw P (c.m - 1)) St)) ∧
      c.θ / (2 * c.m) *
        (2 * ((c.m : ℝ) - 1) * CappedBaseStock.mean P + expectedShortfall P.law Sh
          + expectedShortfall P.law St - expectedShortfall (maxLaw P (c.m - 1)) Sh
          + expectedShortfall (maxLaw P (c.m - 1)) St
          - 2 * expectedShortfall (leadTimeLaw P (c.m - 1)) St)
        ≤ ((c.m : ℝ) - 1) * c.θ / c.m * CappedBaseStock.mean P := by sorry

end PerishBaseStock.Lifo
