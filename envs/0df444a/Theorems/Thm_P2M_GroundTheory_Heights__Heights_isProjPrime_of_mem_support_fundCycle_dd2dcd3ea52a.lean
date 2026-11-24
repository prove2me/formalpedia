-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_of_mem_support_fundCycle_dd2dcd3ea52a
-- name    : P2M_GroundTheory_Heights__Heights_isProjPrime_of_mem_support_fundCycle_dd2dcd3ea52a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:24.715063+00:00
-- url     : https://prove2.me/theorems/69ddae36-e458-4083-b5d6-83d20cea2aff
-- title:
--   P2 M Ground Theory Heights  Heights is Proj Prime of mem support fund Cycle dd2dcd3ea52a: P2 M Ground Theory Heights  Heights is Proj Prime of mem support fund Cycle dd2dcd3ea52a
-- statement:
--   The P2 M Ground Theory Heights  Heights is Proj Prime of mem support fund Cycle dd2dcd3ea52a construction uses the P2 M Ground Theory Heights  Heights is Proj Prime of mem support fund Cycle dd2dcd3ea52a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L105-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L105-L126

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

theorem P2M_GroundTheory_Heights__Heights_isProjPrime_of_mem_support_fundCycle_dd2dcd3ea52a {J : Ideal (MvPolynomial (Fin n) R)} (hJ : IsHomogIdeal J)
    {W : Ideal (MvPolynomial (Fin n) R)} (hW : W ∈ (fundCycle J).support) : IsProjPrime W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isProjPrime_of_mem_support_fundCycle» := P2M_GroundTheory_Heights__Heights_isProjPrime_of_mem_support_fundCycle_dd2dcd3ea52a
