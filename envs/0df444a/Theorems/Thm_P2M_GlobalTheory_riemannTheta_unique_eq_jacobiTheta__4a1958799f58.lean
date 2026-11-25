-- Prove2me | Theorems.Thm_P2M_GlobalTheory_riemannTheta_unique_eq_jacobiTheta__4a1958799f58
-- name    : P2M_GlobalTheory_riemannTheta_unique_eq_jacobiTheta__4a1958799f58
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:09.019257+00:00
-- url     : https://prove2.me/theorems/f26e7755-a57b-516a-af59-e3d6cfca2954
-- title:
--   P2 M Global Theory riemann Theta unique eq jacobi Theta  4a1958799f58: P2 M Global Theory riemann Theta unique eq jacobi Theta  4a1958799f58
-- statement:
--   The P2 M Global Theory riemann Theta unique eq jacobi Theta  4a1958799f58 construction uses the P2 M Global Theory riemann Theta unique eq jacobi Theta  4a1958799f58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L733-L743
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L733-L743

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ]

theorem P2M_GlobalTheory_riemannTheta_unique_eq_jacobiTheta__4a1958799f58 [Unique ι] (a b : ι → ℝ) (Ω : Matrix ι ι ℂ)
    (v : ι → ℂ) :
    riemannTheta a b Ω v =
      cexp (π * I * (a default) ^ 2 * Ω default default +
        2 * π * I * a default * (v default + b default)) *
      jacobiTheta₂ (v default + b default + a default * Ω default default) (Ω default default) := by sorry

alias «GlobalTheory».«riemannTheta_unique_eq_jacobiTheta₂» := P2M_GlobalTheory_riemannTheta_unique_eq_jacobiTheta__4a1958799f58
