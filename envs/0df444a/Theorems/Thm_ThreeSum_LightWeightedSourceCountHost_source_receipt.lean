-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_source_receipt
-- name    : ThreeSum.LightWeightedSourceCountHost.source_receipt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:51:36.92506+00:00
-- url     : https://prove2.me/theorems/ce4e71e3-9055-4418-8ff8-5d3515c53bac
-- title:
--   Light Weighted Source Count Host: source receipt
-- statement:
--   Direct conversion of the existing source-host execution theorem into the
--   bank reads needed above. All physical source records retain their original
--   positions and coefficients; the run's join order is existentially hidden.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L211-L242
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L211-L242

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_Submission_Weighted_SourceCountHost
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedSourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedSourceCountHost.source_receipt {lim : Limits} {P : Program}
    {p d t N M NL NR bank groups valueBase factor keep hits : ℕ}
    (argv : List ℤ) (μ : ℕ → ℤ) (input dictionary : ℕ → ℤ)
    (enumeration : ℕ → TernaryJointType.TritWord N)
    (key group : ℕ → ℕ) (weight : ℕ → ℤ)
    (hkey : ∀ j<NR, key j<bank)
    (hinj : ∀ i j, i<bank → j<bank → enumeration i=enumeration j → i=j)
    (hfactor : ∀ pair∈TernarySourceHostModel.records M NL NR input dictionary,
      (factor : ℤ)=TernaryConvolution.factorial (enumeration (key pair.2)))
    (h : Meets lim P p d argv μ t
      (fun r ν => r=(valueBase : ℤ) ∧ Kept μ ν keep ∧
        ∃ ps : List (ℕ × ℕ), ps.length=hits ∧ ps.Nodup ∧
          (∀ i j, (i,j)∈ps ↔ i<NL ∧ j<NR ∧ (M : ℤ)∣input i-dictionary j) ∧
          ∀ r<groups*bank, ν (valueBase+r)=(factor : ℤ)*
            LightTernaryWeightedHistogram.total
              (fun i => group (ps.getD i (0,0)).2*bank+key (ps.getD i (0,0)).2)
              (fun i => weight (ps.getD i (0,0)).1) r hits)) :
    Meets lim P p d argv μ t (fun _ ν => Kept μ ν keep ∧
      BankReads ν valueBase groups bank (fun g r =>
        TernaryConvolution.factorial (enumeration r)*
        TernarySourceHostModel.physical
          (TernarySourceHostModel.records M NL NR input dictionary)
          enumeration key group weight g (enumeration r))) := by sorry
