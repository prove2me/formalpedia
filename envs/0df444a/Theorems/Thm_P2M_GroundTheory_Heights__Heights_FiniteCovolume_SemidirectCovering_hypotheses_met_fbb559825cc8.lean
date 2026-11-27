-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_SemidirectCovering_hypotheses_met_fbb559825cc8
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_SemidirectCovering_hypotheses_met_fbb559825cc8
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:33:18.285682+00:00
-- url     : https://prove2.me/theorems/c12dba83-9d93-5f54-a786-95311cae35bb
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Semidirect Covering hypotheses met fbb559825cc8: P2 M Ground Theory Heights  Heights Finite Covolume Semidirect Covering hypotheses met fbb559825cc8
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Semidirect Covering hypotheses met fbb559825cc8 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Semidirect Covering hypotheses met fbb559825cc8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsSemidirectCovering.lean#L30-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsSemidirectCovering.lean#L30-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsSemidirectCovering
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Topology
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_SemidirectCovering_hypotheses_met_fbb559825cc8 : ∃ (i : C2 →* C2 × C2) (q : C2 × C2 →* C2)
    (j : C2 →* C2 × C2) (μL : Measure C2) (_ : μL.IsHaarMeasure) (μN : Measure C2)
    (_ : μN.IsHaarMeasure) (Γ : Subgroup (C2 × C2)) (C : Set C2) (T : Set C2)
    (ν : Measure (C2 × C2)) (_ : ν.IsHaarMeasure),
    Continuous i ∧ Continuous q ∧ IsClosedEmbedding j ∧ (∀ l, q (i l) = l) ∧
    (∀ g, q g = 1 ↔ g ∈ j.range) ∧
    (∀ l, μN.map (fun n => i l * j n * (i l)⁻¹) = μN.map j) ∧ IsCompact C ∧ MeasurableSet T ∧
    μL T < ⊤ ∧ (∀ n, ∃ δ, j δ ∈ Γ ∧ δ * n ∈ C) ∧ (∀ l, ∃ γ ∈ Γ, q γ * l ∈ T) ∧
    i ≠ 1 ∧ j ≠ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«SemidirectCovering».«hypotheses_met» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_SemidirectCovering_hypotheses_met_fbb559825cc8
