-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Geo_emb_form
-- name    : PositivityTheory.ThKF0.Geo.emb_form
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:04:04.593209+00:00
-- url     : https://prove2.me/theorems/8d89c60f-e2d4-4f3d-82c4-27eb119486c7
-- title:
--   Geo: emb form
-- statement:
--   The Geo construction uses the emb form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/GeoAlg.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/GeoAlg.lean#L81-L83

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_GeoAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM Module
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Geo
variable {F : Type} [Field F] {A : Type} [CommRing A] [Algebra F A]

theorem PositivityTheory.ThKF0.Geo.emb_form {κ : Type} [Fintype κ] (a b : (κ → F) × (κ → F)) :
    (emb A κ a).1 ⬝ᵥ (emb A κ b).2 - (emb A κ b).1 ⬝ᵥ (emb A κ a).2 = algebraMap F A (om F κ a b) := by sorry
