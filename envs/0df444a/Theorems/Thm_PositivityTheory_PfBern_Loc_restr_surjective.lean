-- Prove2me | Theorems.Thm_PositivityTheory_PfBern_Loc_restr_surjective
-- name    : PositivityTheory.PfBern.Loc.restr_surjective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:08:04.417355+00:00
-- url     : https://prove2.me/theorems/27560d15-ad7b-460c-84c4-b9a13961f8eb
-- title:
--   Loc: restr surjective
-- statement:
--   The Loc construction uses the restr surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L179-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L179-L182

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
variable {Z : Set X}
variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

theorem PositivityTheory.PfBern.Loc.restr_surjective (hZ : IsClosed Z) : Function.Surjective (restr hZ) := by sorry
