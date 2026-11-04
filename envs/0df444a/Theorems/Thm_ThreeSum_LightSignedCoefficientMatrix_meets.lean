-- Prove2me | Theorems.Thm_ThreeSum_LightSignedCoefficientMatrix_meets
-- name    : ThreeSum.LightSignedCoefficientMatrix.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:45:24.059467+00:00
-- url     : https://prove2.me/theorems/31c91454-c64e-4f4b-ba5a-6dfbb3f80615
-- title:
--   Light Signed Coefficient Matrix: meets
-- statement:
--   The Light Signed Coefficient Matrix construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedCoefficientMatrix.lean#L15-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedCoefficientMatrix.lean#L15-L73

import Definitions.Def_Submission_ThreeSum_LightSignedCoefficientLayout
import Definitions.Def_Submission_ThreeSum_LightSignedCoefficientMatrix
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightSignedCoefficientLayout_meets
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedCoefficientMatrix
open Light
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightSignedCoefficientMatrix.meets {proc pRow src dst rows J U : ℕ}
    (hp : P[proc]?=some (body pRow)) (hrow : P[pRow]?=some LightSignedCoefficientLayout.body)
    (μ : ℕ → ℤ) (f : ℕ → ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth < lim.depth)
    (hsrc : src+rows*(J+2) ≤ dst) (hspace : dst+rows*(J+2) ≤ lim.space)
    (hread : ∀ r < rows, ∀ i < J+2, μ (src+r*(J+2)+i)=f r i)
    (hf : ∀ r < rows, ∀ i < J+2, |f r i| ≤ (U : ℤ))
    (hword : (U : ℤ) ≤ lim.word)
    (hrowsWord : (rows : ℤ) ≤ lim.word) (hJWord : ((J+2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P proc depth [src,dst,rows,J] μ (time rows J)
      (fun _ ν => (∀ r < rows, ∀ i < J+2,
        ν (dst+r*(J+2)+i)=f r (TernarySignedLayout.offset J i)) ∧
        SameOutside μ ν dst (rows*(J+2))) := by sorry
