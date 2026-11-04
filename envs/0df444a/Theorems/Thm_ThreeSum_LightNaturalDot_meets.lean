-- Prove2me | Theorems.Thm_ThreeSum_LightNaturalDot_meets
-- name    : ThreeSum.LightNaturalDot.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:29.035448+00:00
-- url     : https://prove2.me/theorems/c3a92620-39ac-4ef7-838d-9b24b2d490f7
-- title:
--   Light Natural Dot: meets
-- statement:
--   The Light Natural Dot construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNaturalDot.lean#L27-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNaturalDot.lean#L27-L73

import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_LightNaturalDot
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightNaturalDot
open Light Finset
open scoped BigOperators
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightNaturalDot.meets {proc srcA srcB n U V : ℕ} (hp : P[proc]?=some body)
    (μ : ℕ → ℤ) (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word)
    (hA : srcA+n≤lim.space) (hB : srcB+n≤lim.space)
    (hreadA : ∀ i<n, μ (srcA+i)=(f i : ℤ))
    (hreadB : ∀ i<n, μ (srcB+i)=(g i : ℤ))
    (hf : ∀ i<n, f i≤U) (hg : ∀ i<n, g i≤V)
    (hword : (((n+1)*(U+1)*(V+1)+10 : ℕ) : ℤ)≤lim.word) :
    Meets lim P proc depth [srcA,srcB,n] μ (time n)
      (fun r ν => r=(dot f g n : ℤ) ∧ ν=μ) := by sorry
