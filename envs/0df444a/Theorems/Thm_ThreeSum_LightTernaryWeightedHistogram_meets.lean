-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_meets
-- name    : ThreeSum.LightTernaryWeightedHistogram.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:27:28.935186+00:00
-- url     : https://prove2.me/theorems/776b5947-126f-4898-953f-b1adf51f498b
-- title:
--   Light Ternary Weighted Histogram: meets
-- statement:
--   The Light Ternary Weighted Histogram construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedHistogram.lean#L141-L174
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedHistogram.lean#L141-L174

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWeightedHistogram
open Light Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryWeightedHistogram.meets {pMain pFill keys pairs source n dst bank sourceCount U : ℕ}
    (hmain : P[pMain]?=some (body pFill)) (hfill : P[pFill]?=some fillBody)
    (μ : ℕ → ℤ) (key position : ℕ → ℕ) (weight : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hkeys : keys+n ≤ dst) (hpairs : pairs+2*n ≤ dst)
    (hsource : source+sourceCount ≤ dst) (hdst : dst+bank ≤ lim.space)
    (hkeyRead : ∀ i < n, μ (keys+i) = (key i : ℤ))
    (hposRead : ∀ i < n, μ (pairs+2*i) = (position i : ℤ))
    (hsourceRead : ∀ i < n, μ (source+position i) = weight i)
    (hkeyLt : ∀ i < n, key i < bank) (hposLt : ∀ i < n, position i < sourceCount)
    (hweights : ∀ i < n, |weight i| ≤ U)
    (hword : ((n+1 : ℕ) : ℤ)*U ≤ lim.word) :
    Meets lim P pMain d [keys,pairs,source,n,dst,bank,sourceCount] μ (time n bank)
      (fun _ ν => (∀ r < bank, ν (dst+r)=total key weight r n) ∧
        SameOutside μ ν dst bank) := by sorry
