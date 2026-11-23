-- Prove2me | Theorems.Thm_P2M_GlobalTheory_hasDerivAt_canonicalSigma__ab13341749ec
-- name    : P2M_GlobalTheory_hasDerivAt_canonicalSigma__ab13341749ec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:40.098431+00:00
-- url     : https://prove2.me/theorems/5bf0ee62-5eb7-49d4-8c9e-a26c8323652d
-- title:
--   P2 M Global Theory has Deriv At canonical Sigma  ab13341749ec: P2 M Global Theory has Deriv At canonical Sigma  ab13341749ec
-- statement:
--   The P2 M Global Theory has Deriv At canonical Sigma  ab13341749ec construction uses the P2 M Global Theory has Deriv At canonical Sigma  ab13341749ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L1013-L1018
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L1013-L1018

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)

theorem P2M_GlobalTheory_hasDerivAt_canonicalSigma__ab13341749ec (z : ℂ) : HasDerivAt (canonicalSigma L)
    ((deriv (weierstrassSigma L) z - sTwo L * z * weierstrassSigma L z) *
      cexp (-(sTwo L * z ^ 2 / 2))) z := by sorry

alias «GlobalTheory».«hasDerivAt_canonicalSigma'» := P2M_GlobalTheory_hasDerivAt_canonicalSigma__ab13341749ec
