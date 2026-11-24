-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_coord_ne_zero_8ba8fb65c857
-- name    : P2M_GroundTheory_Heights__Heights_StandardModelDualRank_coord_ne_zero_8ba8fb65c857
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:35:06.863471+00:00
-- url     : https://prove2.me/theorems/39728dba-67ab-4608-9cb5-3911f2e0d41b
-- title:
--   P2 M Ground Theory Heights  Heights Standard Model Dual Rank coord ne zero 8ba8fb65c857: P2 M Ground Theory Heights  Heights Standard Model Dual Rank coord ne zero 8ba8fb65c857
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Model Dual Rank coord ne zero 8ba8fb65c857 construction uses the P2 M Ground Theory Heights  Heights Standard Model Dual Rank coord ne zero 8ba8fb65c857 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L139-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardModelDualRank.lean#L139-L142

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField DualArithmeticVariety
noncomputable section
open GroundTheory.Heights₂.Heights.StandardModelDualRank
variable {K : Type} [Field K] {i : ℕ}
variable [NumberField K]
variable {T : Type}

theorem P2M_GroundTheory_Heights__Heights_StandardModelDualRank_coord_ne_zero_8ba8fb65c857 (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (t : T) :
    dualStdModelEmb K i (dualLatticeCoord b ⟨(), t⟩) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardModelDualRank».«coord_ne_zero» := P2M_GroundTheory_Heights__Heights_StandardModelDualRank_coord_ne_zero_8ba8fb65c857
