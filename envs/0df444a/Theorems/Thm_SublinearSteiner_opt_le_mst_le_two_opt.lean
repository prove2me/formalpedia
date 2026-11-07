-- Prove2me | Theorems.Thm_SublinearSteiner_opt_le_mst_le_two_opt
-- name    : SublinearSteiner.opt_le_mst_le_two_opt
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:43:48.437881+00:00
-- url     : https://prove2.me/theorems/ae2d560b-1572-4e9c-b9f9-9d05a7d5ae39
-- title:
--   $\mathrm{OPT}\le L\le2\,\mathrm{OPT}$
-- statement:
--   Let $(V,T,w)$ be an instance of the metric Steiner tree problem, let $\mathrm{OPT}$ be the least weight of a tree whose vertex set contains $T$, and let $L$ be the weight of a minimum spanning tree of the metric restricted to $T$. Then
--   $$\mathrm{OPT}\le L\le2\,\mathrm{OPT}.$$
--   This is the factor-2 baseline which the mission's goal improves, and it is used in Proposition 4.9.
--
--   Differences from the source:
--   - encoding: L for T empty is not discussed → L = 0 for empty T; reason: a default for a case the page does not use; OPT = 0 there
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Section 1, p.1

import Mathlib
import Definitions.Def_SublinearSteiner_FinMetric

namespace SublinearSteiner

/-- Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027 submission (manuscript sha256 ae133037…), Section 1, p.1: "Doubling a Steiner tree and shortcutting gives `OPT ≤ L ≤ 2OPT`".

**Formalization Note.** `IsSteinerOpt` forces `n ≥ 1`. For `|T| ≤ 1` both costs are `0`. -/
theorem opt_le_mst_le_two_opt {n : ℕ} (w : FinMetric n) (T : Finset (Fin n)) (OPT L : ℝ)
    (hOPT : IsSteinerOpt T w OPT) (hL : IsTerminalMST T w L) : OPT ≤ L ∧ L ≤ 2 * OPT := by sorry

end SublinearSteiner
