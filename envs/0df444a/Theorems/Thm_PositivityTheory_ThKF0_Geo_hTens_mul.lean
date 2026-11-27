-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Geo_hTens_mul
-- name    : PositivityTheory.ThKF0.Geo.hTens_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:00:51.204804+00:00
-- url     : https://prove2.me/theorems/5c9885a0-0e7c-4f3e-9d52-9b41cdf6dd5c
-- title:
--   Geo: h Tens mul
-- statement:
--   The Geo construction uses the h Tens mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/GeoAlg.lean#L259-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/GeoAlg.lean#L259-L268

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

theorem PositivityTheory.ThKF0.Geo.hTens_mul (JA : Matrix α α E) (JB : Matrix β β E) (a : Matrix α α' E) (b : Matrix β β' E) (x y : Matrix α' β' E) :
    hTens c JA JB (a * x * bᵀ) (a * y * bᵀ) = hTens c (aᵀ * JA * a.map c) (bᵀ * JB * b.map c) x y := by sorry
