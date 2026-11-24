-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_term_le_cb387f1df1fe
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_term_le_cb387f1df1fe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:58.053782+00:00
-- url     : https://prove2.me/theorems/cf085e8e-d804-4c6b-85b5-2d1984e09668
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum term le cb387f1df1fe: P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum term le cb387f1df1fe
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum term le cb387f1df1fe construction uses the P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum term le cb387f1df1fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PPrimeLogSum.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PPrimeLogSum.lean#L11-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PPrimeLogSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open Finset
open GroundTheory.Heights₂.Heights.NineStatements.PrimeLogSum

theorem P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_term_le_cb387f1df1fe {p : ℕ} (hp : 2 ≤ p) :
    Real.log p / ((p : ℝ) - 1) ≤ 2 * (Real.log p / p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«PrimeLogSum».«term_le» := P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_term_le_cb387f1df1fe
