-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Geo_schr_add
-- name    : PositivityTheory.ThKF0.Geo.schr_add
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:04:06.483532+00:00
-- url     : https://prove2.me/theorems/b9e43997-c95b-5eb2-95a3-15b8ba6baf90
-- title:
--   Geo: schr add
-- statement:
--   The Geo construction uses the schr add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/GeoAlg.lean#L101-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/GeoAlg.lean#L101-L111

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
variable {VA : Type} [AddCommGroup VA] [Module A VA] [Module F VA] [IsScalarTower F A VA] {BA : VA → VA → A}
  {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module F V]

theorem PositivityTheory.ThKF0.Geo.schr_add [Invertible (2 : A)] (ψ : AddChar A ℂ) (a b : (κ → A) × (κ → A))
    (h : a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 = 0) (φ : (κ → A) → ℂ) : schr ψ (a + b) φ = schr ψ a (schr ψ b φ) := by sorry
