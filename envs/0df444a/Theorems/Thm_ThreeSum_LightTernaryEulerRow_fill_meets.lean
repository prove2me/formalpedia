-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEulerRow_fill_meets
-- name    : ThreeSum.LightTernaryEulerRow.fill_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:25.864033+00:00
-- url     : https://prove2.me/theorems/2c2612e7-fd7c-4b33-9748-41d4fc58174c
-- title:
--   Light Ternary Euler Row: fill meets
-- statement:
--   The Light Ternary Euler Row construction uses the fill meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerRow.lean#L95-L147
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerRow.lean#L95-L147

import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedSum
import Definitions.Def_Submission_ThreeSum_LightTernaryDivide
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerRow
import Theorems.Thm_Light_fill_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerRow
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryEulerRow.fill_meets
    {pMain pRow pSum pDivide pNaturalDivide ws ks table N pcount Mo V fr U dst : ℕ}
    {q : ℤ}
    (hmain : P[pMain]? = some (fillBody pRow))
    (hrow : P[pRow]? = some (body pSum pDivide))
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
    (hdst : dst < fr) (hd : d+3 ≤ lim.depth) :
    Meets lim P pMain d [ws,ks,table,N,pcount,Mo,fr,dst] μ (fillTime N V)
      (fun r μ' => r=q ∧ μ' dst=q ∧
        ∀ a < fr, a ≠ dst → μ' a=μ a) := by sorry
