-- Prove2me | Theorems.Thm_ThreeSumSharpTail_pruned_encoding_comparison
-- name    : ThreeSumSharpTail.pruned_encoding_comparison
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T17:38:15.176137+00:00
-- url     : https://prove2.me/theorems/e8e4e1a1-9f72-4d34-918e-23238f797f5c
-- title:
--   Pruned encoding exponent is bounded by the original encoding exponent
-- statement:
--   For every real c>1, the exponent ((c/2)H(1/c)+(c-1)log(3))/log(4) is at most A(c). Consequently the strict thinness assumption in the sharp-tail certificate also satisfies the encoding assumption of the parameterized pruned program interface. This comparison follows from the weighted log inequality H(p)+(1-p)log(9)<=log(10).
-- source:
--   Derived auxiliary inequality for Xu, same manuscript, Section 4, encodingbound; the pruned exponent Apruned is defined in the existing platform module APSP299791_Defs4, source ThreeSumApsp/Pruned/Costs.lean at formal-math commit 27a2fa4bab32. It is not an additional theorem claimed in the manuscript.

import Definitions.Def_ThreeSumSharpTail_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem ThreeSumSharpTail.pruned_encoding_comparison (c : ℝ) (hc : 1 < c) :
    ((c / 2) * ThreeSumSharpTail.entropy (1 / c) + (c - 1) * Real.log 3) / Real.log 4
      ≤ ThreeSumSharpTail.encodingExponent c := by sorry
