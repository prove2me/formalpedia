-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_smallBlockTwo_m1Prime_0200493cebd2
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_smallBlockTwo_m1Prime_0200493cebd2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:43.368276+00:00
-- url     : https://prove2.me/theorems/0b7aae12-261f-5241-b78c-0570a18b9353
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements small Block Two m1 Prime 0200493cebd2: P2 M Ground Theory Heights  Heights Nine Statements small Block Two m1 Prime 0200493cebd2
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements small Block Two m1 Prime 0200493cebd2 construction uses the P2 M Ground Theory Heights  Heights Nine Statements small Block Two m1 Prime 0200493cebd2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigen.lean#L142-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigen.lean#L142-L170

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

theorem P2M_GroundTheory_Heights__Heights_NineStatements_smallBlockTwo_m1Prime_0200493cebd2 {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]
    (ι : E →+* L) {j' : ℕ} (hj : 1 ≤ j') {S : Finset ℕ} (h2 : 2 ∈ S) :
    OrderBoundAtPrime (fun _ => ι) j' S (smallBlockTwo ι) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«smallBlockTwo_m1Prime» := P2M_GroundTheory_Heights__Heights_NineStatements_smallBlockTwo_m1Prime_0200493cebd2
