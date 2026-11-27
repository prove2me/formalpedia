-- Prove2me | Theorems.Thm_PositivityTheory_PfBern_Loc_isEquivariant_extendDistr
-- name    : PositivityTheory.PfBern.Loc.isEquivariant_extendDistr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:50:32.251687+00:00
-- url     : https://prove2.me/theorems/1a881980-fa6c-52fe-8ecf-25506f8c529b
-- title:
--   Loc: is Equivariant extend Distr
-- statement:
--   The Loc construction uses the is Equivariant extend Distr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L199-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L199-L205

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
variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [TotallyDisconnectedSpace Y]
omit [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [T2Space Y]
  [LocallyCompactSpace Y]

theorem PositivityTheory.PfBern.Loc.isEquivariant_extendDistr {ι : Type*} {p : X → Y} (hp : Continuous p)
    (e : ι → X ≃ₜ X) (χ : ι → ℂ) (he : ∀ i x, p (e i x) = p x) (y : Y)
    (D' : Distr (p ⁻¹' {y})) (hD' : IsEquivariant (fun i => fiberHomeo (e i) (he i) y) χ D') :
    IsEquivariant e χ (extendDistr (isClosed_singleton.preimage hp) D') := by sorry
