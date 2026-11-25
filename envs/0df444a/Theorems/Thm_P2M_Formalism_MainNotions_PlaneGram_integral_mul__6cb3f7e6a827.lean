-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_integral_mul__6cb3f7e6a827
-- name    : P2M_Formalism_MainNotions_PlaneGram_integral_mul__6cb3f7e6a827
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:01:03.246873+00:00
-- url     : https://prove2.me/theorems/cc8bef46-ec39-47b5-968a-1a3a89dddd9d
-- title:
--   P2 M Formalism Main Notions Plane Gram integral mul  6cb3f7e6a827: P2 M Formalism Main Notions Plane Gram integral mul  6cb3f7e6a827
-- statement:
--   The P2 M Formalism Main Notions Plane Gram integral mul  6cb3f7e6a827 construction uses the P2 M Formalism Main Notions Plane Gram integral mul  6cb3f7e6a827 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/IntegralMonomial.lean#L40-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/IntegralMonomial.lean#L40-L49

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsMonomialOrder
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial
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
variable {K : Type} [Field K] {v : AddValuation K (WithTop ℚ)} {σ : Type}

theorem P2M_Formalism_MainNotions_PlaneGram_integral_mul__6cb3f7e6a827 {F G : MvPolynomial σ K} (hF : Integral v F) (hG : Integral v G) :
    Integral v (F * G) := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«integral_mul'» := P2M_Formalism_MainNotions_PlaneGram_integral_mul__6cb3f7e6a827
