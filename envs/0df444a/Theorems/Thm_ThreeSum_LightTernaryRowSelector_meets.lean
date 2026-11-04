-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryRowSelector_meets
-- name    : ThreeSum.LightTernaryRowSelector.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:24:14.358067+00:00
-- url     : https://prove2.me/theorems/535f681c-3556-4b97-b73d-8ec50277bc79
-- title:
--   Light Ternary Row Selector: meets
-- statement:
--   The Light Ternary Row Selector construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRowSelector.lean#L71-L151
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRowSelector.lean#L71-L151

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_TernaryPairedSelector
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRowSelector
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryRowSelector.meets {p flagBase a₀ a₁ a₂ n U d₀ d₁ d₂ t₀ t₁ t₂ : ℕ}
    (hprog : P[p]? = some body) (μ : ℕ → ℤ)
    (flag f₀ f₁ f₂ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hflagSpace : flagBase+n ≤ lim.space) (h₀ : a₀+n ≤ lim.space)
    (h₁ : a₁+n ≤ lim.space) (h₂ : a₂+n ≤ lim.space)
    (hflag : ∀ i<n, μ (flagBase+i)=flag i ∧ |flag i|≤1)
    (hread₀ : ∀ i<n, μ (a₀+i)=f₀ i ∧ |f₀ i|≤U)
    (hread₁ : ∀ i<n, μ (a₁+i)=f₁ i ∧ |f₁ i|≤U)
    (hread₂ : ∀ i<n, μ (a₂+i)=f₂ i ∧ |f₂ i|≤U)
    (hword : (word n U d₀ d₁ d₂ t₀ t₁ t₂ : ℤ) ≤ lim.word) :
    Meets lim P p d [flagBase,a₀,a₁,a₂,n,d₀,d₁,d₂,t₀,t₁,t₂] μ (time n)
      (fun r μ' => r=(pick (Good flag f₀ f₁ f₂ d₀ d₁ d₂ t₀ t₁ t₂) n : ℤ) ∧ μ'=μ) := by sorry
