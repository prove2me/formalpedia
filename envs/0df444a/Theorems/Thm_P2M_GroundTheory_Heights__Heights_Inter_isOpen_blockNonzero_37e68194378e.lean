-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isOpen_blockNonzero_37e68194378e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_isOpen_blockNonzero_37e68194378e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:17.709826+00:00
-- url     : https://prove2.me/theorems/609545f8-d46a-4fd8-84d5-dcfbf335ffb9
-- title:
--   P2 M Ground Theory Heights  Heights Inter is Open block Nonzero 37e68194378e: P2 M Ground Theory Heights  Heights Inter is Open block Nonzero 37e68194378e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter is Open block Nonzero 37e68194378e construction uses the P2 M Ground Theory Heights  Heights Inter is Open block Nonzero 37e68194378e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRSlotAdd.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRSlotAdd.lean#L18-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMixSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRSlotAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_isOpen_blockNonzero_37e68194378e : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«isOpen_blockNonzero» := P2M_GroundTheory_Heights__Heights_Inter_isOpen_blockNonzero_37e68194378e
