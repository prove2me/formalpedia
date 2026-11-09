-- Prove2me | Theorems.Thm_SparseIncidenceHom_WidthComparison_fractional_separator_cost_le_adaptive_width
-- name    : SparseIncidenceHom.WidthComparison.fractional_separator_cost_le_adaptive_width
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:14.040067+00:00
-- url     : https://prove2.me/theorems/f894ba38-457a-488e-8fb8-bc6dfb39c67b
-- title:
--   Lemma 3.4 — hereditary fractional separator cost is at most adaptive width
-- statement:
--   For every finite covered hypergraph $H$, including empty or disconnected induced hypergraphs,
--   $$\operatorname{fsep}_{1/2}(H)\le\operatorname{adw}(H).$$
--   Here $\operatorname{fsep}$ takes the supremum over every projected induced hypergraph $H[W]$ and every nonzero real edge weighting into $[0,1]$. Adaptive width independently takes the supremum over edge-dominated modular weightings of their minimum decomposition width. No common modular witness or balanced bag is assumed in this theorem. The hereditary conclusion supplies the fractional separator bound used by the goal.
--
--   Differences from the source:
--   - encoding: finite hypergraphs with the standing coverage and nonempty-edge conventions → Mathlib hypergraphs on an arbitrary finite carrier, with the full carrier as vertex set and explicit coverage and nonempty-edge fields; reason: every source hypergraph is represented by choosing its vertex set as carrier, including empty and disconnected induced hypergraphs
--   - encoding: minima over tree decompositions, fractional covers and feasible fractional separators → real infima of their attained cost sets; finite bag maxima and bounded modular suprema; reason: finite covered hypergraphs have feasible covers and decompositions; separator feasibility is compact with continuous cover value; all relevant extrema are finite and the minima are attained
--   - encoding: a nonnegative hereditary supremum, with zero for the empty family → a real supremum with the singleton zero included; reason: the costs are nonnegative and bounded, so adjoining zero leaves every nonempty-family supremum unchanged and gives the specified empty convention
-- source:
--   Matthias Lanzinger, STOC 2027 submission #662 (October 2026), p. 12, Lemma 3.4

import Mathlib
import Definitions.Def_SparseIncidenceHom_WidthComparison_Separators

namespace SparseIncidenceHom.WidthComparison

theorem fractional_separator_cost_le_adaptive_width {V : Type} [Fintype V]
    (H : FiniteHypergraph V) :
    hereditarySeparatorCost H (1 / 2) ≤ adaptiveWidth H := by sorry

end SparseIncidenceHom.WidthComparison
