-- Prove2me | Theorems.Thm_PositivityTheory_PfBern_Loc_pullL_pullL_symm
-- name    : PositivityTheory.PfBern.Loc.pullL_pullL_symm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:08:54.091805+00:00
-- url     : https://prove2.me/theorems/0b30d5e2-0fe4-4910-b6fb-49fb36934615
-- title:
--   Loc: pull L pull L symm
-- statement:
--   The Loc construction uses the pull L pull L symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L272-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L272-L273

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FiberLocalization_EqZeroOfFiberEquivariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Loc
variable {X : Type*} [TopologicalSpace X]
variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

theorem PositivityTheory.PfBern.Loc.pullL_pullL_symm (h : A ≃ₜ B) (f : SC A) : pullL h (pullL h.symm f) = f := by sorry
