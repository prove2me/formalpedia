-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalRepeatWordAddress_canonical_address
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalRepeatWordAddress.canonical_address
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:41:27.363194+00:00
-- url     : https://prove2.me/theorems/0268497f-5aa5-41e5-902c-5f82e09d8a82
-- title:
--   canonical_address
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryRepeatWordAddress.lean#L32-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryRepeatWordAddress.lean#L32-L47

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryRepeatWord
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryRepeatWordAddress
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalRepeatWordAddress
open ThreeSum.LightTernaryRepeatWord
open TernaryJointType
set_option maxHeartbeats 2000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalRepeatWordAddress.canonical_address {L : ℕ} (Q : TritWord L) (r : ℕ) :
    value (TernaryCodeSemantics.address Q) (4^L) r=
      TernaryCodeSemantics.address (WeightedGlobalRepeatedWords.canonical (fun _ : Fin r=>Q)) := by sorry
