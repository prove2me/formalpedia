-- Prove2me | Theorems.Thm_PositivityTheory_PfBern_Loc_extendDistr_apply
-- name    : PositivityTheory.PfBern.Loc.extendDistr_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:57:18.851835+00:00
-- url     : https://prove2.me/theorems/350a508d-81d3-5bfa-90c3-2aaf10960b43
-- title:
--   Loc: extend Distr apply
-- statement:
--   The Loc construction uses the extend Distr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L168-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L168-L170

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

theorem PositivityTheory.PfBern.Loc.extendDistr_apply (hZ : IsClosed Z) (D' : Distr Z) (f : SC X) :
    extendDistr hZ D' f = D' (restr hZ f) := by sorry
