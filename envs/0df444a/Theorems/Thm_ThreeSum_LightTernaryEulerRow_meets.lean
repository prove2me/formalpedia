-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
-- name    : ThreeSum.LightTernaryEulerRow.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:29:29.636564+00:00
-- url     : https://prove2.me/theorems/87cd949a-a6f5-444e-8edf-a1f09a70f95b
-- title:
--   Light Ternary Euler Row: meets
-- statement:
--   Correctness is from the stored predecessor values and the exact Euler
--   identity for the desired row.  Key-scoped bounds permit bank and memo values
--   to occupy separate physical regions, without copying the bank per query.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerRow.lean#L31-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerRow.lean#L31-L76

import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedSum
import Definitions.Def_Submission_ThreeSum_LightTernaryDivide
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerRow
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerRow
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryEulerRow.meets {pMain pSum pDivide pNaturalDivide ws ks table N pcount Mo V fr U : ℕ}
    {q : ℤ}
    (hmain : P[pMain]? = some (body pSum pDivide))
    (hsum : P[pSum]? = some LightTernaryWeightedSum.body)
    (hdivide : P[pDivide]? = some (LightTernaryDivide.body pNaturalDivide))
    (hnatural : P[pNaturalDivide]? = some LightOutputDecodeDivide.body)
    (μ : ℕ → ℤ) (weights keys : ℕ → ℕ) (f : ℕ → ℤ)
    (F : Light.Emod.Pre lim Mo V fr)
    (hws : ws+N ≤ lim.space) (hks : ks+N ≤ lim.space)
    (htable : table+pcount ≤ lim.space)
    (hweights : ∀ i < N, μ (ws+i) = (weights i : ℤ))
    (hkeys : ∀ i < N, μ (ks+i) = (keys i : ℤ))
    (hrange : ∀ i < N, keys i < pcount)
    (hread : ∀ i < N, μ (table+keys i) = f (keys i))
    (hweight : ∀ i < N, weights i ≤ 2)
    (hvalue : ∀ i < N, |f (keys i)| ≤ U)
    (hV : 2*(N+1)*U ≤ V)
    (hEuler : LightTernaryWeightedSum.sum weights keys f N = (Mo : ℤ)*q)
    (hd : d+2 ≤ lim.depth) :
    Meets lim P pMain d [ws,ks,table,N,pcount,Mo,fr] μ (time N V)
      (fun r μ' => r=q ∧ Kept μ μ' fr) := by sorry
