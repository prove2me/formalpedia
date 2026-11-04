-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_count_ends
-- name    : ThreeSum.LightTernaryWeightedHistogram.count_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:19.565031+00:00
-- url     : https://prove2.me/theorems/62bc4f3a-f931-4951-b950-a11a0769b7ed
-- title:
--   Light Ternary Weighted Histogram: count ends
-- statement:
--   The Light Ternary Weighted Histogram construction uses the count ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedHistogram.lean#L51-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedHistogram.lean#L51-L135

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram
import Definitions.Def_WeightedCache3SUM_Alias_c744ea44a98f0b41

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWeightedHistogram
open Light Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryWeightedHistogram.count_ends {μ : ℕ → ℤ} {loc : ℕ → ℤ}
    {keys pairs source n dst bank sourceCount U : ℕ}
    (key position : ℕ → ℕ) (weight : ℕ → ℤ)
    (hloc : loc 0=keys ∧ loc 1=pairs ∧ loc 2=source ∧ loc 3=n ∧ loc 4=dst)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hkeys : keys+n ≤ dst) (hpairs : pairs+2*n ≤ dst)
    (hsource : source+sourceCount ≤ dst) (hdst : dst+bank ≤ lim.space)
    (hkeyRead : ∀ i < n, μ (keys+i) = (key i : ℤ))
    (hposRead : ∀ i < n, μ (pairs+2*i) = (position i : ℤ))
    (hsourceRead : ∀ i < n, μ (source+position i) = weight i)
    (hkeyLt : ∀ i < n, key i < bank) (hposLt : ∀ i < n, position i < sourceCount)
    (hzero : ∀ r < bank, μ (dst+r)=0)
    (hweights : ∀ i < n, |weight i| ≤ U)
    (hword : ((n+1 : ℕ) : ℤ)*U ≤ lim.word) :
    Ends lim P d countBody ⟨loc,μ⟩ (countTime n) (fun σ' =>
      (∀ r < bank, σ'.mem (dst+r)=total key weight r n) ∧
        SameOutside μ σ'.mem dst bank) := by sorry
