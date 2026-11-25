-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_finrank_jacSpanAt_eq
-- name    : ReciprocityTheory.AnForm.R.finrank_jacSpanAt_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:06:08.115698+00:00
-- url     : https://prove2.me/theorems/560e5a0a-bc5f-5a71-88c8-d2093b66957b
-- title:
--   R: finrank jac Span At eq
-- statement:
--   The R construction uses the finrank jac Span At eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartB.lean#L38-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartB.lean#L38-L61

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial IsLocalRing

theorem ReciprocityTheory.AnForm.R.finrank_jacSpanAt_eq {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) :
    Module.finrank ℂ (jacSpanAt I z) =
      Module.finrank ℂ (jacSpan (I.map (renR σ : MvPolynomial σ ℂ →+* _)) (renPt z)) := by sorry
