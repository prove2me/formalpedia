-- Prove2me | Theorems.Thm_ThreeSum_LightCoverUpdate_meets_w3sum_ac885d1
-- name    : ThreeSum.LightCoverUpdate.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:24:32.00689+00:00
-- url     : https://prove2.me/theorems/aa002c3c-da6e-4945-964e-b82a081d7d59
-- title:
--   Light Cover Update: meets
-- statement:
--   The Light Cover Update construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverUpdate.lean#L17-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverUpdate.lean#L17-L60

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightCoverUpdate
set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverUpdate
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightCoverUpdate.meets_w3sum_ac885d1 {p : ℕ} (hp : P[p]? = some body)
    {μ : ℕ → ℤ} {row activePtr n : ℕ} (cover active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hrow : row+n ≤ lim.space) (hactive : activePtr+n ≤ lim.space)
    (hsep : Apart row n activePtr n)
    (hread : ∀ j < n, μ (row+j) = (cover j : ℤ))
    (hreadActive : ∀ j < n, μ (activePtr+j) = (active j : ℤ))
    (hcover : ∀ j < n, cover j ≤ 1) (hact : ∀ j < n, active j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P p d [row,activePtr,n] μ (time n)
      (fun _ μ' => (∀ j < n, μ' (activePtr+j) = ((active j*(1-cover j) : ℕ) : ℤ)) ∧
        SameOutside μ μ' activePtr n) := by sorry
