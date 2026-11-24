-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_segre_const_b90202405c1e
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_segre_const_b90202405c1e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:38.817198+00:00
-- url     : https://prove2.me/theorems/ec4909fb-6e6b-4ae7-a913-997f770e9bd2
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Mass At Point segre const b90202405c1e: P2 M Ground Theory Heights  Heights Standard Dual Mass At Point segre const b90202405c1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Mass At Point segre const b90202405c1e construction uses the P2 M Ground Theory Heights  Heights Standard Dual Mass At Point segre const b90202405c1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdMassAt.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdMassAt.lean#L18-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.StandardDualMassAtPoint
variable {K : Type} [Field K] [NumberField K] {T : Type} [Fintype T] [DecidableEq T]
omit [Fintype T] [DecidableEq T]

theorem P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_segre_const_b90202405c1e (z : (Σ _ : Unit, T) → ℂ) (t : T) :
    segre (ι := dualBlocks T) z (fun _ => t) = z ⟨(), t⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualMassAtPoint».«segre_const» := P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_segre_const_b90202405c1e
