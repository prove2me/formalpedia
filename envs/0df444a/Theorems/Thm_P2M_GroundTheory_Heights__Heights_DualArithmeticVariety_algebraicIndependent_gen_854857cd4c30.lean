-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_algebraicIndependent_gen_854857cd4c30
-- name    : P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_algebraicIndependent_gen_854857cd4c30
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:25.020489+00:00
-- url     : https://prove2.me/theorems/edb7b838-965b-4ba3-a80b-daa2791cff6b
-- title:
--   P2 M Ground Theory Heights  Heights Dual Arithmetic Variety algebraic Independent gen 854857cd4c30: P2 M Ground Theory Heights  Heights Dual Arithmetic Variety algebraic Independent gen 854857cd4c30
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Arithmetic Variety algebraic Independent gen 854857cd4c30 construction uses the P2 M Ground Theory Heights  Heights Dual Arithmetic Variety algebraic Independent gen 854857cd4c30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualArithVar.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualArithVar.lean#L18-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualArithmeticVariety
variable {K : Type} [Field K]

theorem P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_algebraicIndependent_gen_854857cd4c30 (m : ℕ) :
    AlgebraicIndependent K fun j : Fin m =>
      algebraMap (MvPolynomial (Fin m) K) (ProjField K m) (X j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualArithmeticVariety».«algebraicIndependent_gen» := P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_algebraicIndependent_gen_854857cd4c30
