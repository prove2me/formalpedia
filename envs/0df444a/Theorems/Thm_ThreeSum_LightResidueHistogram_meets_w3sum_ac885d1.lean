-- Prove2me | Theorems.Thm_ThreeSum_LightResidueHistogram_meets_w3sum_ac885d1
-- name    : ThreeSum.LightResidueHistogram.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:20.384847+00:00
-- url     : https://prove2.me/theorems/b4e359df-b9d3-48fa-8f7a-958030ec1dce
-- title:
--   Light Residue Histogram: meets
-- statement:
--   The Light Residue Histogram construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidueHistogram.lean#L121-L156
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidueHistogram.lean#L121-L156

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
set_option autoImplicit false
open ThreeSum ThreeSum.LightResidueHistogram
open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightResidueHistogram.meets_w3sum_ac885d1 {pMain pResidues pEmod pHistogram pFill : ℕ}
    (hmain : P[pMain]? = some (body pResidues pHistogram))
    (hres : P[pResidues]? = some (residuesBody pEmod))
    (hem : P[pEmod]? = some emodBody)
    (hhist : P[pHistogram]? = some (histogramBody pFill))
    (hfill : P[pFill]? = some fillBody)
    {μ : ℕ → ℤ} {src dst n p cap codes work U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth)
    (hp : 0 < p) (hcap : p ≤ cap)
    (hsrc : src + n ≤ codes) (hdst : dst + cap ≤ codes)
    (hcodes : codes + n ≤ work)
    (hspace : work + (Nat.log 2 (U + 1) + 2) ≤ lim.space)
    (hc : |c| ≤ 1) (hword : (4 * U + 4 * p + 16 : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src + i)| ≤ (U : ℤ)) :
    Meets lim P pMain d [src, dst, n, p, cap, codes, work, c] μ (time n cap U)
      fun _ μ' =>
        Seg μ' dst (padTo cap (vector p (signedHistogram p c (fun i => μ (src+i)) n))) ∧
          KeptBut μ μ' codes dst cap := by sorry
