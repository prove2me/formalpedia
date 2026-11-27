-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_SemidirectCovering_proof_41357b0bc592
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_SemidirectCovering_proof_41357b0bc592
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:13:09.037915+00:00
-- url     : https://prove2.me/theorems/a090a0bf-f453-5354-8f4b-e27b86c298d0
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Semidirect Covering proof 41357b0bc592: P2 M Ground Theory Heights  Heights Finite Covolume Semidirect Covering proof 41357b0bc592
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Semidirect Covering proof 41357b0bc592 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Semidirect Covering proof 41357b0bc592 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PSemidirectCovering.lean#L11-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PSemidirectCovering.lean#L11-L95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsSemidirectCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PSemidirectCovering
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory MeasureTheory.Measure Topology
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_SemidirectCovering_proof_41357b0bc592 (H L N : Type*) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    [LocallyCompactSpace L] [SecondCountableTopology L] [T2Space L] [MeasurableSpace L]
    [BorelSpace L] [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N]
    [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] :
    SemidirectCovering.Statement H L N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«SemidirectCovering».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_SemidirectCovering_proof_41357b0bc592
