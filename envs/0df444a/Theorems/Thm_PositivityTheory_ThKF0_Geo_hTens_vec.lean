-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Geo_hTens_vec
-- name    : PositivityTheory.ThKF0.Geo.hTens_vec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:00:34.176798+00:00
-- url     : https://prove2.me/theorems/dd5678cc-347a-4475-bc3c-3a31c4e742f4
-- title:
--   Geo: h Tens vec
-- statement:
--   The Geo construction uses the h Tens vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/GeoAlg.lean#L270-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/GeoAlg.lean#L270-L278

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
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β α' β' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype α'] [DecidableEq α']
  [Fintype β'] [DecidableEq β']

theorem PositivityTheory.ThKF0.Geo.hTens_vec (JA : Matrix α α E) (JB : Matrix β β E) (w : Matrix α β E) (a : α → E) (b : β → E) :
    hTens c JA JB w (vecMulVec a b) = (JA *ᵥ fun i => c (a i)) ⬝ᵥ (w *ᵥ (JB *ᵥ fun i => c (b i))) := by sorry
