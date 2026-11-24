-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_primeFrac_ne_zero_6c9de5626853
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_primeFrac_ne_zero_6c9de5626853
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:40.580418+00:00
-- url     : https://prove2.me/theorems/0ae5a4c0-ec2a-4b91-a3d2-bfb904be8302
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements prime Frac ne zero 6c9de5626853: P2 M Ground Theory Heights  Heights Nine Statements prime Frac ne zero 6c9de5626853
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements prime Frac ne zero 6c9de5626853 construction uses the P2 M Ground Theory Heights  Heights Nine Statements prime Frac ne zero 6c9de5626853 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigenInputs.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigenInputs.lean#L71-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem P2M_GroundTheory_Heights__Heights_NineStatements_primeFrac_ne_zero_6c9de5626853 (L : Type) [Field L] [NumberField L] {q : ℕ} (hq : q.Prime) : primeFrac L q ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«primeFrac_ne_zero» := P2M_GroundTheory_Heights__Heights_NineStatements_primeFrac_ne_zero_6c9de5626853
