-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionSeedMatrix_meets
-- name    : ThreeSum.LightExtensionSeedMatrix.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:27:16.058474+00:00
-- url     : https://prove2.me/theorems/3cc7082b-07fd-4d29-acaa-638ed12feef6
-- title:
--   Light Extension Seed Matrix: meets
-- statement:
--   The Light Extension Seed Matrix construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionSeedMatrix.lean#L30-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionSeedMatrix.lean#L30-L115

import Definitions.Def_Submission_ThreeSum_LightExtensionSeedRow
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedMatrix
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightExtensionSeedRow_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionSeedMatrix
open Light
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightExtensionSeedMatrix.meets {proc pRow pDigit pDivide table q p dst len : ℕ}
    (hp : P[proc]?=some (body pRow pDigit pDivide))
    (hrow : P[pRow]?=some (LightExtensionSeedRow.body pDigit))
    (hdigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (mul : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth+2 < lim.depth)
    (hq : 0 < q) (hmod : 0 < p)
    (htable : table+q*q ≤ dst) (hspace : dst+q*q*len ≤ lim.space)
    (hread : ∀ a < q, ∀ b < q, μ (table+a*q+b)=(mul a b : ℤ))
    (hmul : ∀ a < q, ∀ b < q, mul a b < q)
    (hword : (word len q p : ℤ) ≤ lim.word) :
    Meets lim P proc depth [table,q,p,dst,len] μ (time len q)
      (fun _ ν => (∀ i < q*q, ∀ j < len, ν (dst+i*len+j)=(value mul q p i j : ℤ)) ∧
        SameOutside μ ν dst (q*q*len)) := by sorry
