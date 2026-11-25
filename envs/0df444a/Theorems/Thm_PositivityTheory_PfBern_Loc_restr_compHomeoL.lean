-- Prove2me | Theorems.Thm_PositivityTheory_PfBern_Loc_restr_compHomeoL
-- name    : PositivityTheory.PfBern.Loc.restr_compHomeoL
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:56:08.706727+00:00
-- url     : https://prove2.me/theorems/909a46ce-7653-5b36-9713-7fda33066698
-- title:
--   Loc: restr comp Homeo L
-- statement:
--   The Loc construction uses the restr comp Homeo L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L172-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FiberLocalization/EqZeroOfFiberEquivariant.lean#L172-L175

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

theorem PositivityTheory.PfBern.Loc.restr_compHomeoL (hZ : IsClosed Z) (e : X ≃ₜ X) (heZ : ∀ x, x ∈ Z ↔ e x ∈ Z)
    (f : SC X) :
    restr hZ (compHomeoL e f) = compHomeoL (e.subtype heZ) (restr hZ f) := by sorry
