-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_SemidirectHaar_proof_026c949566ef
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_SemidirectHaar_proof_026c949566ef
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:55:50.476263+00:00
-- url     : https://prove2.me/theorems/028baa21-dd5d-52e1-949e-41c5f20b63d4
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Semidirect Haar proof 026c949566ef: P2 M Ground Theory Heights  Heights Finite Covolume Semidirect Haar proof 026c949566ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Semidirect Haar proof 026c949566ef construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Semidirect Haar proof 026c949566ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PSemidirectHaar.lean#L11-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PSemidirectHaar.lean#L11-L196

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsSemidirectHaar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PSemidirectHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_SemidirectHaar_proof_026c949566ef (G T : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] :
    SemidirectHaar.Statement G T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«SemidirectHaar».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_SemidirectHaar_proof_026c949566ef
