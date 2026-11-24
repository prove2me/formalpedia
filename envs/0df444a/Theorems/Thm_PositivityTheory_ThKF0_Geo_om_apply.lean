-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Geo_om_apply
-- name    : PositivityTheory.ThKF0.Geo.om_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:57.781726+00:00
-- url     : https://prove2.me/theorems/8dd45257-5a5e-41f4-a090-4163b136c1bc
-- title:
--   Geo: om apply
-- statement:
--   The Geo construction uses the om apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/GeoAlg.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/GeoAlg.lean#L20-L20

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
variable {F : Type} [Field F] {κ : Type} [Fintype κ]

theorem PositivityTheory.ThKF0.Geo.om_apply (w w' : (κ → F) × (κ → F)) : om F κ w w' = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 := by sorry
