-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Geo_emb_apply
-- name    : PositivityTheory.ThKF0.Geo.emb_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:45.104475+00:00
-- url     : https://prove2.me/theorems/851688f5-2cba-4d02-aa45-3eb4bb11716b
-- title:
--   Geo: emb apply
-- statement:
--   The Geo construction uses the emb apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/GeoAlg.lean#L72-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/GeoAlg.lean#L72-L73

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

theorem PositivityTheory.ThKF0.Geo.emb_apply {κ : Type} (w : (κ → F) × (κ → F)) :
    emb A κ w = (fun i => algebraMap F A (w.1 i), fun i => algebraMap F A (w.2 i)) := by sorry
