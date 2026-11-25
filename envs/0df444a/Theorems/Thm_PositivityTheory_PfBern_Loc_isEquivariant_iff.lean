-- Prove2me | Theorems.Thm_PositivityTheory_PfBern_Loc_isEquivariant_iff
-- name    : PositivityTheory.PfBern.Loc.isEquivariant_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:52:30.429274+00:00
-- url     : https://prove2.me/theorems/2ebb4b4f-1cf4-5810-9dc0-d02cae8821c6
-- title:
--   Loc: is Equivariant iff
-- statement:
--   The Loc construction uses the is Equivariant iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L96-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L96-L108

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
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [TotallyDisconnectedSpace Y]

theorem PositivityTheory.PfBern.Loc.isEquivariant_iff {ι : Type*} (e : ι → X ≃ₜ X) (χ : ι → ℂ) (D : Distr X) :
    IsEquivariant e χ D ↔ ∀ w ∈ relSpanH e χ, D w = 0 := by sorry
