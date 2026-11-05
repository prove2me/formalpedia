-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_branches_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.branches_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:08:23.865682+00:00
-- url     : https://prove2.me/theorems/290101c4-a788-412e-bec3-7a26e136632b
-- title:
--   branches_meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrozenBranches.lean#L36-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrozenBranches.lean#L36-L115

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Enumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Frozen
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenBranches
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery
open Light ThreeSum.TernaryQuery
open ThreeSum.WeightedEnumeration (digitCost)
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.branches_meets {pSelf d : ℕ}
    (N K rank cut bankCodes bankCount bankValues nearCodes nearCount nearValues powers L : ℕ)
    (code c0 c1 : ℤ) (q : Fin 3) (f : Fin 3 → ℤ) (t : Fin 3 → ℕ)
    (μ : ℕ → ℤ)
    (hargs : ∀ x ∈ preparedInputs N K rank cut code bankCodes bankCount bankValues
      nearCodes nearCount nearValues powers L q c0 c1, |x| ≤ lim.word)
    (hword : 4 * (max (|f 0|) (max (|f 1|) (|f 2|))) + 3 ≤ lim.word)
    (hrank : digitCost q.val ≤ rank) (hd : d+1 ≤ lim.depth)
    (hchild : ∀ r : Fin 3, r ≤ q → Meets lim P pSelf (d+1)
      (inputs N K (rank-(digitCost q.val-digitCost r.val)) cut
        (if r=0 then c0 else if r=1 then c1 else code)
        bankCodes bankCount bankValues nearCodes nearCount nearValues powers L) μ (t r)
      (fun v μ' => v=f r ∧ μ'=μ)) :
    Ends lim P d (branches pSelf) ⟨frame (preparedInputs N K rank cut code bankCodes bankCount bankValues
      nearCodes nearCount nearValues powers L q c0 c1),μ⟩
      (t 0+t 1+t 2+200)
      (fun σ => σ.loc 0 = inverseDigit f q ∧ σ.mem=μ) := by sorry
