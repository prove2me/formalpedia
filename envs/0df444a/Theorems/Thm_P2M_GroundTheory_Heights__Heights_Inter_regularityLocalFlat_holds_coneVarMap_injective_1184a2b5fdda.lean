-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_injective_1184a2b5fdda
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_injective_1184a2b5fdda
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:31.039862+00:00
-- url     : https://prove2.me/theorems/dee19e98-5e38-4900-ba61-e087e4964e52
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds cone Var Map injective 1184a2b5fdda: P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds cone Var Map injective
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds cone Var Map injective 1184a2b5fdda construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds cone Var Map injective 1184a2b5fdda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L122-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L122-L145

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsLocalizationConeVarMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]
variable {P W}

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_injective_1184a2b5fdda (hPW : P ≤ W) (hPh : IsMultiHomogIdeal P) {v : ∀ k, ι k}
    (hv : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ W) : Function.Injective (coneVarMap P W hPW v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalFlat_holds».«coneVarMap_injective» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_injective_1184a2b5fdda
