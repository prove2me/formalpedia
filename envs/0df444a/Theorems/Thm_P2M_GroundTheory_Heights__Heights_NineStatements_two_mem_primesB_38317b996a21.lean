-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_two_mem_primesB_38317b996a21
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_two_mem_primesB_38317b996a21
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:05:25.979773+00:00
-- url     : https://prove2.me/theorems/e3453df8-b5b9-4aff-a663-457a44180344
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements two mem primes B 38317b996a21: P2 M Ground Theory Heights  Heights Nine Statements two mem primes B 38317b996a21
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements two mem primes B 38317b996a21 construction uses the P2 M Ground Theory Heights  Heights Nine Statements two mem primes B 38317b996a21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigen.lean#L172-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigen.lean#L172-L174

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigen
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

theorem P2M_GroundTheory_Heights__Heights_NineStatements_two_mem_primesB_38317b996a21 {B : ℕ} (hB : 2 ≤ B) (bad : Finset ℕ) : 2 ∈ primesB B bad := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«two_mem_primesB» := P2M_GroundTheory_Heights__Heights_NineStatements_two_mem_primesB_38317b996a21
