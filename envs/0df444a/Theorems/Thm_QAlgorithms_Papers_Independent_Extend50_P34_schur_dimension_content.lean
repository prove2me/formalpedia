-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_schur_dimension_content
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.schur_dimension_content
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:46:34.495504+00:00
-- url     : https://prove2.me/theorems/a95a0711-f123-4acf-82c2-6b3e22744101
-- title:
--   Proposition 2.11
-- statement:
--   For any partition $\lambda$ and positive integer $d$, write $\dim\lambda$ for its Specht dimension and $d^{\uparrow\lambda}=\prod_{\square\in\lambda}(d+c(\square))$. Then
--
--   $$s_\lambda(1^d)=\frac{\dim\lambda}{|\lambda|!}\,d^{\uparrow\lambda}.$$
--
--   This includes the empty partition and heights greater than $d$, where both sides vanish. It relates unitary-group dimensions to Specht dimensions.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 15, Proposition 2.11

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Proposition 2.11, arXiv:1501.05028v1, PDF p.15.  -/
theorem schur_dimension_content
    (lambda : YoungDiagram) (d : ℕ) (hd : 0 < d) :
    schurAt lambda (fun _ : Fin d => 1) =
      (dim lambda : ℝ) * contentProduct d lambda / lambda.card.factorial := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
