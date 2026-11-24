-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_mem_of_gen_mem_a23b53b6b97d
-- name    : P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_mem_of_gen_mem_a23b53b6b97d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:40.494473+00:00
-- url     : https://prove2.me/theorems/4347cf46-e445-454d-a8a9-5b494998f6b4
-- title:
--   P2 M Ground Theory Heights  Heights Dual Arithmetic Variety mem of gen mem a23b53b6b97d: P2 M Ground Theory Heights  Heights Dual Arithmetic Variety mem of gen mem a23b53b6b97d
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Arithmetic Variety mem of gen mem a23b53b6b97d construction uses the P2 M Ground Theory Heights  Heights Dual Arithmetic Variety mem of gen mem a23b53b6b97d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualArithVar.lean#L32-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualArithVar.lean#L32-L44

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

theorem P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_mem_of_gen_mem_a23b53b6b97d {m : ℕ} (E : IntermediateField K (ProjField K m))
    (h : ∀ j, algebraMap (MvPolynomial (Fin m) K) (ProjField K m) (X j) ∈ E) (z : ProjField K m) :
    z ∈ E := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualArithmeticVariety».«mem_of_gen_mem» := P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_mem_of_gen_mem_a23b53b6b97d
