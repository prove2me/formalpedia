-- Prove2me | Theorems.Thm_PositivityTheory_PfBern_Frob_mem_SB_iff
-- name    : PositivityTheory.PfBern.Frob.mem_SB_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:56.422804+00:00
-- url     : https://prove2.me/theorems/46596e19-d46a-42f2-b6b1-693437c12831
-- title:
--   Frob: mem SB iff
-- statement:
--   The Frob construction uses the mem SB iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FrobeniusReciprocity/PullHomeoApply.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FrobeniusReciprocity/PullHomeoApply.lean#L15-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_PullHomeoApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set GlobalTheory.SplitWeil
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Frob

theorem PositivityTheory.PfBern.Frob.mem_SB_iff {X : Type*} [TopologicalSpace X] {f : X → ℂ} :
    f ∈ SB X ↔ IsLocallyConstant f ∧ HasCompactSupport f := by sorry
