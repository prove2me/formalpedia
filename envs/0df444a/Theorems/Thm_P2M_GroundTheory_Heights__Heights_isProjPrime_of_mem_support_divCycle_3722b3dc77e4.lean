-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_of_mem_support_divCycle_3722b3dc77e4
-- name    : P2M_GroundTheory_Heights__Heights_isProjPrime_of_mem_support_divCycle_3722b3dc77e4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:22.828727+00:00
-- url     : https://prove2.me/theorems/3ca18944-7768-4dbf-b7be-3c6d2cd0cb86
-- title:
--   P2 M Ground Theory Heights  Heights is Proj Prime of mem support div Cycle 3722b3dc77e4: P2 M Ground Theory Heights  Heights is Proj Prime of mem support div Cycle 3722b3dc77e4
-- statement:
--   The P2 M Ground Theory Heights  Heights is Proj Prime of mem support div Cycle 3722b3dc77e4 construction uses the P2 M Ground Theory Heights  Heights is Proj Prime of mem support div Cycle 3722b3dc77e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L128-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L128-L131

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type*} [CommRing R] {n : ℕ}
variable [IsNoetherianRing R]

theorem P2M_GroundTheory_Heights__Heights_isProjPrime_of_mem_support_divCycle_3722b3dc77e4 {I : Ideal (MvPolynomial (Fin n) R)} (hI : IsProjPrime I)
    (u : Fin n → R) {W : Ideal (MvPolynomial (Fin n) R)} (hW : W ∈ (divCycle I u).support) :
    IsProjPrime W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isProjPrime_of_mem_support_divCycle» := P2M_GroundTheory_Heights__Heights_isProjPrime_of_mem_support_divCycle_3722b3dc77e4
