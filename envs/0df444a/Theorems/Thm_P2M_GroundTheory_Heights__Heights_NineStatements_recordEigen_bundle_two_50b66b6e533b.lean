-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_recordEigen_bundle_two_50b66b6e533b
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_recordEigen_bundle_two_50b66b6e533b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:31:54.34291+00:00
-- url     : https://prove2.me/theorems/d1bc1176-da8b-4d50-8c1e-2764ef184314
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements record Eigen bundle two 50b66b6e533b: P2 M Ground Theory Heights  Heights Nine Statements record Eigen bundle two 50b66b6e533b
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements record Eigen bundle two 50b66b6e533b construction uses the P2 M Ground Theory Heights  Heights Nine Statements record Eigen bundle two 50b66b6e533b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigen.lean#L176-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigen.lean#L176-L180

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

theorem P2M_GroundTheory_Heights__Heights_NineStatements_recordEigen_bundle_two_50b66b6e533b {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (ι : E →+* L) :
    2 ≤ 2 ∧ (∀ p ∈ (∅ : Finset ℕ), p.Prime) ∧ (∅ : Finset ℕ).card ≤ 2 ∧
      EigenRecordAt (fun _ => ι) 1 (smallBlockTwo ι) ∧ OrderBoundAtPrime (fun _ => ι) 1 (primesB 2 ∅) (smallBlockTwo ι) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«recordEigen_bundle_two» := P2M_GroundTheory_Heights__Heights_NineStatements_recordEigen_bundle_two_50b66b6e533b
