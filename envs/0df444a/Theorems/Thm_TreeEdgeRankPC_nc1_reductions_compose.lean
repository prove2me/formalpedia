-- Prove2me | Theorems.Thm_TreeEdgeRankPC_nc1_reductions_compose
-- name    : TreeEdgeRankPC.nc1_reductions_compose
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:54.570317+00:00
-- url     : https://prove2.me/theorems/08433fdc-04d7-4272-8fe9-78c797a3f3db
-- title:
--   §3.2 — NC¹ many-one reductions compose
-- statement:
--   If $f$ and $g$ are NC¹-computable functions, so is $g\circ f$. Consequently, if $A$ reduces to $B$ and $B$ reduces to $D$ under NC¹ many-one reductions, then $A$ reduces to $D$.
--
--   This is what lets the two stages of the mission's reduction and the hardness of AM2CVP be chained.
--
--   Differences from the source:
--   - reading: "uniform" family → logspace-uniform family; reason: p.12 defines only this uniformity; a weaker one would make the hardness claim weaker
--   - encoding: NC¹ computation of a polynomial-length string → `NC1Computable`, with (valid bit, data bit) output pairs, size ≤ n^k + k, depth ≤ c·⌊log₂ n⌋ + c, also a circuit for n = 0; reason: the standard padding convention for outputs of varying length; a constant-size circuit for the empty input changes nothing
--   - reading: "These reductions compose" → both composition of NC¹-computable functions and transitivity of `NC1Reducible`; reason: the composition of two reductions is a reduction exactly through these two facts
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), §3.2, p.12 ("These reductions compose.")

import Mathlib
import Definitions.Def_TreeEdgeRankPC_NC1

namespace TreeEdgeRankPC

/-- **NC¹ many-one reductions compose**, §3.2, p.12, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…): "These reductions compose."

**Formalization Note.** Both the composition of the computed functions and the transitivity of the reduction
are stated. Since `|f(x)|` varies among inputs of equal length, the first conjunct is about the padded format of
`NC1Computable`. -/
theorem nc1_reductions_compose :
    (∀ f g : List Bool → List Bool, NC1Computable f → NC1Computable g → NC1Computable (g ∘ f)) ∧
    (∀ A B D : Set (List Bool), NC1Reducible A B → NC1Reducible B D → NC1Reducible A D) := by sorry

end TreeEdgeRankPC
