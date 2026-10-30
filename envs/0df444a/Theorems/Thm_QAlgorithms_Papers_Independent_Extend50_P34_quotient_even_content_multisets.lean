-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_quotient_even_content_multisets
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.quotient_even_content_multisets
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:04:52.834463+00:00
-- url     : https://prove2.me/theorems/48e94377-bf05-40a8-8b34-676aee8d0a1f
-- title:
--   Lemma 4.17
-- statement:
--   For a balanced partition $\mu$ with 2-quotient $(\mu^{(0)},\mu^{(1)})$, the multisets, with all multiplicities retained, satisfy
--
--   $$\{c(\square):\square\in\mu^{(0)}\}\uplus\{c(\square):\square\in\mu^{(1)}\}=\{c(\square)/2:\square\in\mu,\ c(\square)\text{ even}\}.$$
--
--   Contents are signed integers. This identifies the quotient content product needed for alternating Schur evaluation.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 41, Lemma 4.17

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Lemma 4.17, arXiv:1501.05028v1, PDF p.41. The comma in the source means multiset union, not intersection. Quotient runner labels may swap without changing this statement. -/
theorem quotient_even_content_multisets
    (mu : YoungDiagram) (hmu : DominoBalanced mu) :
    ((twoQuotient mu 0).cells.val.map content) +
      ((twoQuotient mu 1).cells.val.map content) =
        (parityCells mu true).val.map (fun c => content c / 2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
