-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_integral_smul__67d1bab69c28
-- name    : P2M_Formalism_MainNotions_PlaneGram_integral_smul__67d1bab69c28
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:00:55.903809+00:00
-- url     : https://prove2.me/theorems/ab80f750-6908-4b9b-a5ed-eebef173bb5e
-- title:
--   P2 M Formalism Main Notions Plane Gram integral smul  67d1bab69c28: P2 M Formalism Main Notions Plane Gram integral smul  67d1bab69c28
-- statement:
--   The P2 M Formalism Main Notions Plane Gram integral smul  67d1bab69c28 construction uses the P2 M Formalism Main Notions Plane Gram integral smul  67d1bab69c28 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/IntegralMonomial.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/IntegralMonomial.lean#L33-L38

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

theorem P2M_Formalism_MainNotions_PlaneGram_integral_smul__67d1bab69c28 {a : K} {F : MvPolynomial σ K} (ha : 0 ≤ v a) (hF : Integral v F) :
    Integral v (a • F) := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«integral_smul'» := P2M_Formalism_MainNotions_PlaneGram_integral_smul__67d1bab69c28
