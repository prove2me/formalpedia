-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_homog_varMono_d425fcc92f17
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_homog_varMono_d425fcc92f17
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:35:05.098533+00:00
-- url     : https://prove2.me/theorems/6c76b3bf-9a21-5e3b-82e7-929e4c869190
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds homog var Mono d425fcc92f17: P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds homog var Mono d425fcc92f17
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds homog var Mono d425fcc92f17 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds homog var Mono d425fcc92f17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L29-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L29-L43

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_homog_varMono_d425fcc92f17 (v : ∀ k, ι k) (e : K →₀ ℕ) : IsMultiHomog (varMono v e : MRing ι) ⇑e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalFlat_holds».«homog_varMono» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_homog_varMono_d425fcc92f17
