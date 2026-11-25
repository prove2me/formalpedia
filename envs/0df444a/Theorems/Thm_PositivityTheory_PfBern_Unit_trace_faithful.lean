-- Prove2me | Theorems.Thm_PositivityTheory_PfBern_Unit_trace_faithful
-- name    : PositivityTheory.PfBern.Unit.trace_faithful
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:51:32.035268+00:00
-- url     : https://prove2.me/theorems/1cd0271e-f3fe-596d-a094-598f9467ca91
-- title:
--   Unit: trace faithful
-- statement:
--   The Unit construction uses the trace faithful property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/UnitaryKirillovModel/LevelSmulSmul.lean#L85-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/UnitaryKirillovModel/LevelSmulSmul.lean#L85-L137

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_UnitaryKirillovModel_LevelSmulSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Unit
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem PositivityTheory.PfBern.Unit.trace_faithful (hρ : IsAdmissible ρ) [ρ.IsIrreducible] (S : Module.End ℂ V)
    (h : ∀ f : locallyConstantCompactSupport G ℂ ℂ, finTrace (heckeLin μ hρ.1 f ∘ₗ S) = 0) : S = 0 := by sorry
