-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_TwistData_Dm_nonneg__77fcfcd038a0
-- name    : P2M_Formalism_MainNotions_PlaneGram_TwistData_Dm_nonneg__77fcfcd038a0
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:01:25.098126+00:00
-- url     : https://prove2.me/theorems/10e205fe-9e65-4280-bf17-adc2ccdf782e
-- title:
--   P2 M Formalism Main Notions Plane Gram Twist Data Dm nonneg  77fcfcd038a0: P2 M Formalism Main Notions Plane Gram Twist Data Dm nonneg  77fcfcd038a0
-- statement:
--   The P2 M Formalism Main Notions Plane Gram Twist Data Dm nonneg  77fcfcd038a0 construction uses the P2 M Formalism Main Notions Plane Gram Twist Data Dm nonneg  77fcfcd038a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CardLinkIdxMulLe.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CardLinkIdxMulLe.lean#L91-L94

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

theorem P2M_Formalism_MainNotions_PlaneGram_TwistData_Dm_nonneg__77fcfcd038a0 {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.Dm p C0 := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«TwistData».«Dm_nonneg'» := P2M_Formalism_MainNotions_PlaneGram_TwistData_Dm_nonneg__77fcfcd038a0
