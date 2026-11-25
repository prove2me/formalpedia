-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_sum_primesB_le_b85d75dee8d5
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_sum_primesB_le_b85d75dee8d5
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:28.48202+00:00
-- url     : https://prove2.me/theorems/161f97b9-2d8d-5da2-9dc8-cf02f8b3e014
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements sum primes B le b85d75dee8d5: P2 M Ground Theory Heights  Heights Nine Statements sum primes B le b85d75dee8d5
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements sum primes B le b85d75dee8d5 construction uses the P2 M Ground Theory Heights  Heights Nine Statements sum primes B le b85d75dee8d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigen.lean#L91-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigen.lean#L91-L110

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

theorem P2M_GroundTheory_Heights__Heights_NineStatements_sum_primesB_le_b85d75dee8d5 {C : ℝ} (h5 : ∀ B : ℕ, 2 ≤ B → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ B →
      ∑ p ∈ P, Real.log p / ((p : ℝ) - 1) ≤ C * Real.log B)
    {B : ℕ} (hB : 2 ≤ B) {bad : Finset ℕ} (hbad : ∀ p ∈ bad, p.Prime) (hcard : bad.card ≤ B) :
    ∑ p ∈ primesB B bad, Real.log p / ((p : ℝ) - 1) ≤ 2 * C * Real.log B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«sum_primesB_le» := P2M_GroundTheory_Heights__Heights_NineStatements_sum_primesB_le_b85d75dee8d5
