-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_dualStdCoordMat_sum_425dd1ff37fe
-- name    : P2M_GroundTheory_Heights__Heights_dualStdCoordMat_sum_425dd1ff37fe
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:54.391798+00:00
-- url     : https://prove2.me/theorems/01671195-a1f9-42cb-a89a-795926781c11
-- title:
--   P2 M Ground Theory Heights  Heights dual Std Coord Mat sum 425dd1ff37fe: P2 M Ground Theory Heights  Heights dual Std Coord Mat sum 425dd1ff37fe
-- statement:
--   The P2 M Ground Theory Heights  Heights dual Std Coord Mat sum 425dd1ff37fe construction uses the P2 M Ground Theory Heights  Heights dual Std Coord Mat sum 425dd1ff37fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/SingleMemDualLatticeStandard.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/SingleMemDualLatticeStandard.lean#L41-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualStdBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_SingleMemDualLatticeStandard
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField Matrix
noncomputable section
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]
omit [DecidableEq T]

theorem P2M_GroundTheory_Heights__Heights_dualStdCoordMat_sum_425dd1ff37fe (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (j : Fin i) :
    ∑ t, dualStdCoordMat b () j t • (b t : Fin i → K) = Pi.single j 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«dualStdCoordMat_sum» := P2M_GroundTheory_Heights__Heights_dualStdCoordMat_sum_425dd1ff37fe
