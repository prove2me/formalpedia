-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_overlap_counterexample
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.overlap_counterexample
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:01:58.001051+00:00
-- url     : https://prove2.me/theorems/2aefe5eb-79b3-4ab0-a59d-29ff64f0418c
-- title:
--   Example 14 / Eqs.(58)–(59): counterexample to the earlier overlap rule
-- statement:
--   For $n=6$, $N=4$, $k=2$ and an integer $d\ge1$, transpose the last two tensor factors and define normalized signals $\sigma_1=d^{-4}V^{(2)}[(45)(36)]$ and $\sigma_2=d^{-4}V^{(2)}[(35)(46)]$. Then
--
--   $$\operatorname{Tr}(\sigma_1\sigma_2)=d^{-4}.$$
--
--   For $d\ge2$ this differs from $d^{-6}$, the value predicted by the earlier overlap rule. Thus identical selected port sets do not by themselves determine the claimed earlier overlap value; the internal pairing structure matters.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 12, Example 14 / Eqs.(58)–(59): counterexample to the earlier overlap rule

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.12, Example 14: true overlap d^-4, versus the incorrect earlier d^-6 rule. -/
theorem overlap_counterexample (d : ℕ) (hd : 1 ≤ d) :
    (mpbtSignal d 4 2 examplePortA * mpbtSignal d 4 2 examplePortB).trace =
      ((d : ℂ)^4)⁻¹ ∧
    (2 ≤ d → (mpbtSignal d 4 2 examplePortA * mpbtSignal d 4 2 examplePortB).trace ≠
      ((d : ℂ)^6)⁻¹) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
