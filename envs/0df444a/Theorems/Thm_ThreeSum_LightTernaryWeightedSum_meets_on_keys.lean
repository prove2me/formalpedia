-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWeightedSum_meets_on_keys
-- name    : ThreeSum.LightTernaryWeightedSum.meets_on_keys
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:23:34.194081+00:00
-- url     : https://prove2.me/theorems/370b6a59-6d87-4c05-9291-4439f016ab25
-- title:
--   Light Ternary Weighted Sum: meets on keys
-- statement:
--   The Light Ternary Weighted Sum construction uses the meets on keys property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedSum.lean#L47-L111
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWeightedSum.lean#L47-L111

import Definitions.Def_Submission_ThreeSum_LightLookupSum
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedSum
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWeightedSum
open Light Finset
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryWeightedSum.meets_on_keys {p ws ks table n pcount U : ℕ}
    (hmain : P[p]? = some body) (μ : ℕ → ℤ)
    (weights keys : ℕ → ℕ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hws : ws+n ≤ lim.space) (hks : ks+n ≤ lim.space)
    (htable : table+pcount ≤ lim.space)
    (hweights : ∀ i < n, μ (ws+i) = (weights i : ℤ))
    (hkeys : ∀ i < n, μ (ks+i) = (keys i : ℤ))
    (hrange : ∀ i < n, keys i < pcount)
    (hread : ∀ i < n, μ (table+keys i) = f (keys i))
    (hweight : ∀ i < n, weights i ≤ 2)
    (hvalue : ∀ i < n, |f (keys i)| ≤ U)
    (hword : 2*(n+1)*(U : ℤ)+3 ≤ lim.word) :
    Meets lim P p d [ws,ks,table,n,pcount] μ (time n)
      (fun r μ' => r = sum weights keys f n ∧ μ' = μ) := by sorry
