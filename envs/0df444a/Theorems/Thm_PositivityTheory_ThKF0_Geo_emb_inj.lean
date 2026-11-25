-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Geo_emb_inj
-- name    : PositivityTheory.ThKF0.Geo.emb_inj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:03:58.094998+00:00
-- url     : https://prove2.me/theorems/05807a7b-8c63-4293-8007-b0e883d5ed82
-- title:
--   Geo: emb inj
-- statement:
--   The Geo construction uses the emb inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/GeoAlg.lean#L75-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/GeoAlg.lean#L75-L79

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

theorem PositivityTheory.ThKF0.Geo.emb_inj (hA : Function.Injective (algebraMap F A)) {κ : Type} : Function.Injective (emb (F := F) A κ) := by sorry
