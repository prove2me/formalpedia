-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_isUnit_coeff_4e53ac3b7cbc
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_isUnit_coeff_4e53ac3b7cbc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:10.00228+00:00
-- url     : https://prove2.me/theorems/ac5fa3de-691b-4afc-b303-7f87fd53c63f
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds exists is Unit coeff 4e53ac3b7cbc: P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds exists is Unit coeff 4e53
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds exists is Unit coeff 4e53ac3b7cbc construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds exists is Unit coeff 4e53ac3b7cbc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L205-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L205-L225

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_isUnit_coeff_4e53ac3b7cbc (hPW : P ≤ W) {v : ∀ k, ι k} (G : MvPolynomial K (locRing P W))
    {g : MRing ι} (hg : g ∉ W)
    (hG : coneVarMap P W hPW v G =
      algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P g)) :
    ∃ e, IsUnit (coeff e G) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalFlat_holds».«exists_isUnit_coeff» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_isUnit_coeff_4e53ac3b7cbc
