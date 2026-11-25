-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_integral_add__439be00d43f6
-- name    : P2M_Formalism_MainNotions_PlaneGram_integral_add__439be00d43f6
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:01:13.290809+00:00
-- url     : https://prove2.me/theorems/398c4d8b-8212-4426-933e-b0edde146c49
-- title:
--   P2 M Formalism Main Notions Plane Gram integral add  439be00d43f6: P2 M Formalism Main Notions Plane Gram integral add  439be00d43f6
-- statement:
--   The P2 M Formalism Main Notions Plane Gram integral add  439be00d43f6 construction uses the P2 M Formalism Main Notions Plane Gram integral add  439be00d43f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/IntegralMonomial.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/IntegralMonomial.lean#L21-L26

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

theorem P2M_Formalism_MainNotions_PlaneGram_integral_add__439be00d43f6 {F G : MvPolynomial σ K} (hF : Integral v F) (hG : Integral v G) :
    Integral v (F + G) := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«integral_add'» := P2M_Formalism_MainNotions_PlaneGram_integral_add__439be00d43f6
