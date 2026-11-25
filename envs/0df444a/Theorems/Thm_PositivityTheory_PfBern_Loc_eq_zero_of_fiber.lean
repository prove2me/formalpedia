-- Prove2me | Theorems.Thm_PositivityTheory_PfBern_Loc_eq_zero_of_fiber
-- name    : PositivityTheory.PfBern.Loc.eq_zero_of_fiber
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:52:20.115795+00:00
-- url     : https://prove2.me/theorems/658a9d52-e4c1-58bb-ac56-f4e61d0b252c
-- title:
--   Loc: eq zero of fiber
-- statement:
--   The Loc construction uses the eq zero of fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L81-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L81-L88

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

theorem PositivityTheory.PfBern.Loc.eq_zero_of_fiber {p : X → Y} (hp : Continuous p) (W : Submodule ℂ (SC X))
    (hW : FiberStable p W)
    (hfib : ∀ (y : Y) (D : Distr X), (∀ w ∈ W, D w = 0) → SupportedIn D (p ⁻¹' {y}) → D = 0)
    (D : Distr X) (hD : ∀ w ∈ W, D w = 0) : D = 0 := by sorry
