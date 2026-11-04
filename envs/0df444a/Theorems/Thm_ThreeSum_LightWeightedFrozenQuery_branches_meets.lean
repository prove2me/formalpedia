-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_branches_meets
-- name    : ThreeSum.LightWeightedFrozenQuery.branches_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:26:44.295002+00:00
-- url     : https://prove2.me/theorems/1909276e-b6e3-489c-80aa-a4ff136768f0
-- title:
--   Light Weighted Frozen Query: branches meets
-- statement:
--   The Light Weighted Frozen Query construction uses the branches meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenBranches.lean#L36-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenBranches.lean#L36-L115

import Definitions.Def_Submission_Weighted_Enumeration
import Definitions.Def_Submission_Weighted_Frozen
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_Weighted_FrozenBranches
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open Light ThreeSum.TernaryQuery
open ThreeSum.WeightedEnumeration (digitCost)
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedFrozenQuery.branches_meets {pSelf d : ℕ}
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
