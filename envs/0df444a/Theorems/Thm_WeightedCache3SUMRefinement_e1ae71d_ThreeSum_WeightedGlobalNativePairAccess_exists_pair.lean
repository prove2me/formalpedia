-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativePairAccess_exists_pair
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairAccess.exists_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:27:56.728368+00:00
-- url     : https://prove2.me/theorems/0092d4ef-38e1-4c01-a1d9-b3368656c390
-- title:
--   exists_pair
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativePairAccess.lean#L42-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativePairAccess.lean#L42-L66

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalNativeCompleteness
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCompactPairedSupport
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairAccess
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairAccess
open Finset TernaryJointType WeightedGlobalNativePairMoments TernarySourceHostModel
set_option maxHeartbeats 2000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairAccess.exists_pair {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (i b c j k : ℕ) (W V : TritWord N)
    (hb : b<S.left.NL) (hc : c<S.right.NL)
    (hj : j<LightTernarySourceHost.size S.left.xs S.left.J)
    (hk : k<LightTernarySourceHost.size S.right.xs S.right.J)
    (hL : S.left.input b=LightTernarySourceHost.dictionary S.left.xs S.left.p0 S.left.J j)
    (hR : S.right.input c=LightTernarySourceHost.dictionary S.right.xs S.right.p0 S.right.J k)
    (hGL : S.left.group j=S.front.group i) (hGR : S.right.group k=S.front.group i)
    (hWL : TernaryCodeSemantics.address (S.front.E.word (S.left.key j))=
      TernaryCodeSemantics.address W)
    (hWR : TernaryCodeSemantics.address (S.front.E.word (S.right.key k))=
      TernaryCodeSemantics.address V)
    (hadd : TernaryConvolution.Adds W V (S.front.Q i)) :
    ∃ p : Pair S i, p.val.1.1=b ∧ p.val.2.1=c := by sorry
