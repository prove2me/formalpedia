-- Prove2me | Theorems.Thm_PositivityTheory_PfBern_Loc_fiberStable_relSpanH
-- name    : PositivityTheory.PfBern.Loc.fiberStable_relSpanH
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:53:16.712481+00:00
-- url     : https://prove2.me/theorems/1feadebf-705e-4c10-b5d4-adef1f945948
-- title:
--   Loc: fiber Stable rel Span H
-- statement:
--   The Loc construction uses the fiber Stable rel Span H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L120-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L120-L129

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
omit [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]

theorem PositivityTheory.PfBern.Loc.fiberStable_relSpanH {ι : Type*} {p : X → Y} (e : ι → X ≃ₜ X) (χ : ι → ℂ)
    (he : ∀ i x, p (e i x) = p x) : FiberStable p (relSpanH e χ) := by sorry
