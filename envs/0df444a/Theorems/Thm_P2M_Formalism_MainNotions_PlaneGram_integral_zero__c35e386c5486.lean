-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_integral_zero__c35e386c5486
-- name    : P2M_Formalism_MainNotions_PlaneGram_integral_zero__c35e386c5486
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:50.213606+00:00
-- url     : https://prove2.me/theorems/0501537a-51e0-4f11-8ed2-ccba0ba826ff
-- title:
--   P2 M Formalism Main Notions Plane Gram integral zero  c35e386c5486: P2 M Formalism Main Notions Plane Gram integral zero  c35e386c5486
-- statement:
--   The P2 M Formalism Main Notions Plane Gram integral zero  c35e386c5486 construction uses the P2 M Formalism Main Notions Plane Gram integral zero  c35e386c5486 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/IntegralMonomial.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/IntegralMonomial.lean#L16-L19

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

theorem P2M_Formalism_MainNotions_PlaneGram_integral_zero__c35e386c5486 : Integral v (0 : MvPolynomial σ K) := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«integral_zero'» := P2M_Formalism_MainNotions_PlaneGram_integral_zero__c35e386c5486
