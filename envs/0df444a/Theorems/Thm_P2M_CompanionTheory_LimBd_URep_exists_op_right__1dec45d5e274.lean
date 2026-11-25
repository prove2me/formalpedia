-- Prove2me | Theorems.Thm_P2M_CompanionTheory_LimBd_URep_exists_op_right__1dec45d5e274
-- name    : P2M_CompanionTheory_LimBd_URep_exists_op_right__1dec45d5e274
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:34.019801+00:00
-- url     : https://prove2.me/theorems/30a724fa-78d3-408d-a13c-81daade0ec95
-- title:
--   P2 M Companion Theory Lim Bd URep exists op right  1dec45d5e274: P2 M Companion Theory Lim Bd URep exists op right  1dec45d5e274
-- statement:
--   The P2 M Companion Theory Lim Bd URep exists op right  1dec45d5e274 construction uses the P2 M Companion Theory Lim Bd URep exists op right  1dec45d5e274 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurOrthogonality.lean#L170-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurOrthogonality.lean#L170-L179

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.URep
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem P2M_CompanionTheory_LimBd_URep_exists_op_right__1dec45d5e274 {π : UnitaryRep G H} {σ : UnitaryRep G K} [Nontrivial H] (hπ : SqInt μ π)
    (hσ : SqInt μ σ) (w : H) (w' : K) :
    ∃ A ∈ π.intertwiners σ, ∀ v v', pairing μ π σ v w v' w' = ⟪v', A v⟫_ℂ := by sorry

alias «CompanionTheory».«LimBd».«URep».«exists_op_right'» := P2M_CompanionTheory_LimBd_URep_exists_op_right__1dec45d5e274
