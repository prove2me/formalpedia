-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_TwistData_Dl_nonneg__c6f8a139e94f
-- name    : P2M_Formalism_MainNotions_PlaneGram_TwistData_Dl_nonneg__c6f8a139e94f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:01:46.089351+00:00
-- url     : https://prove2.me/theorems/75cd3977-6930-4c01-8503-2e381154c35c
-- title:
--   P2 M Formalism Main Notions Plane Gram Twist Data Dl nonneg  c6f8a139e94f: P2 M Formalism Main Notions Plane Gram Twist Data Dl nonneg  c6f8a139e94f
-- statement:
--   The P2 M Formalism Main Notions Plane Gram Twist Data Dl nonneg  c6f8a139e94f construction uses the P2 M Formalism Main Notions Plane Gram Twist Data Dl nonneg  c6f8a139e94f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CardLinkIdxMulLe.lean#L96-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CardLinkIdxMulLe.lean#L96-L102

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CardLinkIdxMulLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)

theorem P2M_Formalism_MainNotions_PlaneGram_TwistData_Dl_nonneg__c6f8a139e94f {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.Dl p C0 := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«TwistData».«Dl_nonneg'» := P2M_Formalism_MainNotions_PlaneGram_TwistData_Dl_nonneg__c6f8a139e94f
