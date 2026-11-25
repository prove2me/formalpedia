-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechExact_proof_3af6e4d7b86c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechExact_proof_3af6e4d7b86c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:48.652161+00:00
-- url     : https://prove2.me/theorems/7158b7ce-e1e4-4091-af2a-b00dbaee48b2
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Exact proof 3af6e4d7b86c: P2 M Ground Theory Heights  Heights Kleiman Cech Exact proof 3af6e4d7b86c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Exact proof 3af6e4d7b86c construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Exact proof 3af6e4d7b86c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L325-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L325-L340

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechExact_proof_3af6e4d7b86c (hdsq : CechDSq.Statement.{u, max u v}) (hdeg : DegLocExact.Statement.{u, v}) :
    CechExact.Statement.{u, v} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechExact».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_CechExact_proof_3af6e4d7b86c
