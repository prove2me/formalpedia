-- Prove2me | Theorems.Thm_PositivityTheory_PfBern_Loc_eq_zero_of_fiber_equivariant_SB
-- name    : PositivityTheory.PfBern.Loc.eq_zero_of_fiber_equivariant_SB
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:52:10.077596+00:00
-- url     : https://prove2.me/theorems/f4d1934a-4a18-4d73-9374-55990ab1ad4f
-- title:
--   Loc: eq zero of fiber equivariant SB
-- statement:
--   The Loc construction uses the eq zero of fiber equivariant SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariantSB.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariantSB.lean#L11-L24

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FiberLocalization_EqZeroOfFiberEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FiberLocalization_EqZeroOfFiberEquivariantSB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Loc

theorem PositivityTheory.PfBern.Loc.eq_zero_of_fiber_equivariant_SB {X : Type*} [TopologicalSpace X] {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
    {ι : Type*} {p : X → Y} (hp : Continuous p)
    (e : ι → X ≃ₜ X) (χ : ι → ℂ) (he : ∀ i x, p (e i x) = p x)
    (hfib : ∀ (y : Y) (D : Module.Dual ℂ (GlobalTheory.SplitWeil.SB X)),
      (∀ (i : ι) (f : GlobalTheory.SplitWeil.SB X),
        D ⟨fun x => (f : X → ℂ) (e i x), f.2.1.comp_continuous (e i).continuous,
          f.2.2.comp_homeomorph (e i)⟩ = χ i * D f) →
      (∀ f : GlobalTheory.SplitWeil.SB X, Function.support (f : X → ℂ) ⊆ (p ⁻¹' {y})ᶜ → D f = 0) → D = 0)
    (D : Module.Dual ℂ (GlobalTheory.SplitWeil.SB X))
    (hD : ∀ (i : ι) (f : GlobalTheory.SplitWeil.SB X),
        D ⟨fun x => (f : X → ℂ) (e i x), f.2.1.comp_continuous (e i).continuous,
          f.2.2.comp_homeomorph (e i)⟩ = χ i * D f) : D = 0 := by sorry
