-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryMomentChannelStep_Procs_meets
-- name    : ThreeSum.LightTernaryMomentChannelStep.Procs.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:54:53.187843+00:00
-- url     : https://prove2.me/theorems/a0effc12-d667-4292-b9ed-f7ea2faedb58
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannelStep.lean#L66-L160
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannelStep.lean#L66-L160

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannels
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentAccumulate_meets
import Theorems.Thm_ThreeSum_LightTernaryScalarChannel_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentChannelStep
open Light TernaryWeightChannels
set_option maxHeartbeats 1500000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryMomentChannelStep.Procs.meets {k j pMain originalB nB originalC nC leftWeight rightWeight
      matrix count out U V hostTime : ℕ} {backend : List ℤ} {positions : List ℕ}
    (S : Procs k j positions (9+backend.length) P pMain)
    (μ : ℕ→ℤ) (B C accum score : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+1<lim.depth)
    (hBspace : originalB+nB≤leftWeight) (hCspace : originalC+nC≤leftWeight)
    (hmatrix : matrix+k*count+count≤leftWeight)
    (hleft : leftWeight+nB≤rightWeight) (hright : rightWeight+nC≤lim.space)
    (houtBefore : leftWeight≤out) (hout : out+count≤lim.space)
    (hleftSpace : leftWeight≤lim.space)
    (hB : ∀ i<nB, μ (originalB+i)=B i) (hC : ∀ i<nC, μ (originalC+i)=C i)
    (hBabs : ∀ i<nB, |B i|≤(U : ℤ)) (hCabs : ∀ i<nC, |C i|≤(U : ℤ))
    (haccum : ∀ i<count, μ (matrix+k*count+i)=accum i)
    (hbounded : ∀ i<count, |accum i|≤(V : ℤ) ∧ |score i|≤(V : ℤ))
    (hleftWord : max (U : ℤ) (2*((k.choose j : ℤ)+1)*((U : ℤ)+2)^j)≤lim.word)
    (hrightWord : max (U : ℤ) (2*((U : ℤ)+1)^(k-j))≤lim.word)
    (haddWord : 2*(V : ℤ)≤lim.word) (hkWord : (k : ℤ)≤lim.word)
    (hpositions : ∀ a∈positions, 9≤a ∧ a<9+backend.length)
    (hargsWord : ∀ z∈args originalB nB originalC nC leftWeight rightWeight matrix count out backend,
      |z|≤lim.word)
    (hhost : ∀ ν, Kept μ ν leftWeight →
      (∀ i<nB, ν (leftWeight+i)=(k.choose j : ℤ)*(-(B i))^j) →
      (∀ i<nC, ν (rightWeight+i)=(C i)^(k-j)) →
      Meets lim P S.pHost (d+1)
        (values positions (args originalB nB originalC nC leftWeight rightWeight matrix count out backend))
        ν hostTime (fun _ ξ => Kept ν ξ leftWeight ∧ ∀ i<count, ξ (out+i)=score i)) :
    Meets lim P pMain d
      (args originalB nB originalC nC leftWeight rightWeight matrix count out backend) μ
      (time k j nB nC count hostTime positions.length)
      (fun r ν => r=0 ∧ (∀ i<count, ν (matrix+k*count+i)=accum i+score i) ∧
        ∀ a<leftWeight, (a<matrix+k*count ∨ matrix+k*count+count≤a) → ν a=μ a) := by sorry
