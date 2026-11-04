-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFinalPreparation_meets
-- name    : ThreeSum.LightTernaryFinalPreparation.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:50:25.897997+00:00
-- url     : https://prove2.me/theorems/5bbc5a0d-340d-4feb-be1c-11c359362a1c
-- title:
--   Light Ternary Final Preparation: meets
-- statement:
--   The Light Ternary Final Preparation construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFinalPreparation.lean#L26-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFinalPreparation.lean#L26-L79

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionScore
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightTernaryFinalPreparation
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryFinalPreparation
open Light LightSubsetAddress
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000
variable {lim : Limits}

theorem ThreeSum.LightTernaryFinalPreparation.meets {keyB nB keyC nC q powers W histB histC d : ℕ}
    (μ : ℕ → ℤ) (keysB keysC : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hkeyB : keyB+nB ≤ powers) (hkeyC : keyC+nC ≤ powers)
    (hpowers : powers+(W+1) ≤ histB) (hhistB : histB+q ≤ histC) (hhistC : histC+q ≤ lim.space)
    (hwordB : ((nB*nB+nB+q+16 : ℕ) : ℤ) ≤ lim.word)
    (hwordC : ((nC*nC+nC+q+16 : ℕ) : ℤ) ≤ lim.word)
    (hpowerWord : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hkeysB : ∀ i < nB, keysB i < q) (hkeysC : ∀ i < nC, keysC i < q)
    (hreadB : ∀ i < nB, μ (keyB+i) = (keysB i : ℤ))
    (hreadC : ∀ i < nC, μ (keyC+i) = (keysC i : ℤ))
    (hd : d+3 ≤ lim.depth) :
    Meets lim program 5 d [keyB,nB,keyC,nC,q,powers,W,histB,histC] μ (time nB nC q W)
      (fun _ ν => Powers ν powers W ∧
        (∀ k < q, ν (histB+k) = (LightHistogram.count keysB k nB : ℤ)) ∧
        (∀ k < q, ν (histC+k) = (LightHistogram.count keysC k nC : ℤ)) ∧
        Kept μ ν powers ∧ (∀ x, Unwritten powers W histB histC q x → ν x = μ x)) := by sorry
