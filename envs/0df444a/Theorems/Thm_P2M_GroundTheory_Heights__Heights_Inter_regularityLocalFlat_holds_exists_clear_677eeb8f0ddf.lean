-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_clear_677eeb8f0ddf
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_clear_677eeb8f0ddf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:42.680461+00:00
-- url     : https://prove2.me/theorems/f70e7724-787a-45bc-90d2-0ec434ec651b
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds exists clear 677eeb8f0ddf: P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds exists clear 677eeb8f0ddf
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds exists clear 677eeb8f0ddf construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds exists clear 677eeb8f0ddf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L65-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L65-L95

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_clear_677eeb8f0ddf (hPW : P ≤ W) (G : MvPolynomial K (locRing P W)) :
    ∃ (V : MRing ι) (b : K → ℕ) (N : (K →₀ ℕ) → MRing ι), IsMultiHomog V b ∧ V ∉ W ∧
      ∀ e, IsMultiHomog (N e) b ∧
        ((coeff e G : locRing P W) : FractionRing (MRing ι ⧸ P)) * fracHom P V = fracHom P (N e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalFlat_holds».«exists_clear» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_clear_677eeb8f0ddf
