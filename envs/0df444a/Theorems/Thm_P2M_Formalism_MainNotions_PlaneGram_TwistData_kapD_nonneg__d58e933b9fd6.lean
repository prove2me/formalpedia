-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_TwistData_kapD_nonneg__d58e933b9fd6
-- name    : P2M_Formalism_MainNotions_PlaneGram_TwistData_kapD_nonneg__d58e933b9fd6
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:01:31.991442+00:00
-- url     : https://prove2.me/theorems/cfafcf87-cbca-4fcd-8e46-2d75577ab2f4
-- title:
--   P2 M Formalism Main Notions Plane Gram Twist Data kap D nonneg  d58e933b9fd6: P2 M Formalism Main Notions Plane Gram Twist Data kap D nonneg  d58e933b9fd6
-- statement:
--   The P2 M Formalism Main Notions Plane Gram Twist Data kap D nonneg  d58e933b9fd6 construction uses the P2 M Formalism Main Notions Plane Gram Twist Data kap D nonneg  d58e933b9fd6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CardLinkIdxMulLe.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CardLinkIdxMulLe.lean#L104-L107

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

theorem P2M_Formalism_MainNotions_PlaneGram_TwistData_kapD_nonneg__d58e933b9fd6 {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) : 0 ≤ D.kapD p := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«TwistData».«kapD_nonneg'» := P2M_Formalism_MainNotions_PlaneGram_TwistData_kapD_nonneg__d58e933b9fd6
