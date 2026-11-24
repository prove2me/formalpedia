-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Geo_eq_zero_of_om
-- name    : PositivityTheory.ThKF0.Geo.eq_zero_of_om
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:39.637257+00:00
-- url     : https://prove2.me/theorems/7eae6353-f354-40d6-bd53-31d86e154210
-- title:
--   Geo: eq zero of om
-- statement:
--   The Geo construction uses the eq zero of om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/GeoAlg.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/GeoAlg.lean#L22-L30

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

theorem PositivityTheory.ThKF0.Geo.eq_zero_of_om (w : (κ → F) × (κ → F)) (h : ∀ w', om F κ w' w = 0) : w = 0 := by sorry
