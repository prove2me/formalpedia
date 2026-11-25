-- Prove2me | Theorems.Thm_PositivityTheory_PfBern_Loc_mulInd_compHomeoL
-- name    : PositivityTheory.PfBern.Loc.mulInd_compHomeoL
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:51:34.712798+00:00
-- url     : https://prove2.me/theorems/aa6b0c7c-318e-553f-9148-76c9f9b8be46
-- title:
--   Loc: mul Ind comp Homeo L
-- statement:
--   The Loc construction uses the mul Ind comp Homeo L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L111-L117

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
omit [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]

theorem PositivityTheory.PfBern.Loc.mulInd_compHomeoL {p : X → Y} (e : X ≃ₜ X) (he : ∀ x, p (e x) = p x) (V : Set Y)
    (hpV : IsClopen (p ⁻¹' V)) (f : SC X) :
    mulInd (p ⁻¹' V) hpV (compHomeoL e f) = compHomeoL e (mulInd (p ⁻¹' V) hpV f) := by sorry
