-- Prove2me | Theorems.Thm_PositivityTheory_PfBern_Loc_eq_zero_of_fiber_equivariant
-- name    : PositivityTheory.PfBern.Loc.eq_zero_of_fiber_equivariant
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:10.345744+00:00
-- url     : https://prove2.me/theorems/3f842a6e-f275-4a57-b9a1-4261048eb7bf
-- title:
--   Loc: eq zero of fiber equivariant
-- statement:
--   The Loc construction uses the eq zero of fiber equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L131-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L131-L137

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

theorem PositivityTheory.PfBern.Loc.eq_zero_of_fiber_equivariant {ι : Type*} {p : X → Y} (hp : Continuous p)
    (e : ι → X ≃ₜ X) (χ : ι → ℂ) (he : ∀ i x, p (e i x) = p x)
    (hfib : ∀ (y : Y) (D : Distr X), IsEquivariant e χ D → SupportedIn D (p ⁻¹' {y}) → D = 0)
    (D : Distr X) (hD : IsEquivariant e χ D) : D = 0 := by sorry
