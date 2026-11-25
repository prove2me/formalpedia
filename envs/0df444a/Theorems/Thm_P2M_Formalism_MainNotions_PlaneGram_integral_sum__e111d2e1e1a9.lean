-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_integral_sum__e111d2e1e1a9
-- name    : P2M_Formalism_MainNotions_PlaneGram_integral_sum__e111d2e1e1a9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:27.352795+00:00
-- url     : https://prove2.me/theorems/4b868178-6972-42e6-bb60-e9edb332ccfe
-- title:
--   P2 M Formalism Main Notions Plane Gram integral sum  e111d2e1e1a9: P2 M Formalism Main Notions Plane Gram integral sum  e111d2e1e1a9
-- statement:
--   The P2 M Formalism Main Notions Plane Gram integral sum  e111d2e1e1a9 construction uses the P2 M Formalism Main Notions Plane Gram integral sum  e111d2e1e1a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/IntegralMonomial.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/IntegralMonomial.lean#L28-L31

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

theorem P2M_Formalism_MainNotions_PlaneGram_integral_sum__e111d2e1e1a9 {κ : Type} (s : Finset κ) (f : κ → MvPolynomial σ K)
    (h : ∀ k ∈ s, Integral v (f k)) : Integral v (∑ k ∈ s, f k) := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«integral_sum'» := P2M_Formalism_MainNotions_PlaneGram_integral_sum__e111d2e1e1a9
