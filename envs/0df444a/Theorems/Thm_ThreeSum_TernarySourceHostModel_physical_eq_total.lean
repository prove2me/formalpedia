-- Prove2me | Theorems.Thm_ThreeSum_TernarySourceHostModel_physical_eq_total
-- name    : ThreeSum.TernarySourceHostModel.physical_eq_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:59.099346+00:00
-- url     : https://prove2.me/theorems/c5c47fe7-d74b-42ed-acee-a89d85e51ad7
-- title:
--   Ternary Source Host Model: physical eq total
-- statement:
--   Actual machine histogram sums reindex to the fixed original-record set.
--   No assumption about the join's enumeration order is needed.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostModel.lean#L59-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostModel.lean#L59-L91

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySourceHostModel
open Finset Light TernaryJointType
open scoped BigOperators
variable {N : ℕ}

theorem ThreeSum.TernarySourceHostModel.physical_eq_total (M NL NR bank : ℕ) (input dictionary : ℕ → ℤ)
    (enumeration : ℕ → TritWord N) (key group : ℕ → ℕ) (weight : ℕ → ℤ)
    (ps : List (ℕ × ℕ)) (hn : ps.Nodup)
    (hmem : ∀ i j, (i,j)∈ps ↔ i<NL ∧ j<NR ∧ (M : ℤ)∣input i-dictionary j)
    (hkey : ∀ j<NR, key j<bank)
    (hinj : ∀ i j, i<bank → j<bank → enumeration i=enumeration j → i=j)
    (g r : ℕ) (hr : r<bank) :
    physical (records M NL NR input dictionary) enumeration key group weight g (enumeration r)=
      LightTernaryWeightedHistogram.total
        (fun i => group (ps.getD i (0,0)).2*bank+key (ps.getD i (0,0)).2)
        (fun i => weight (ps.getD i (0,0)).1) (g*bank+r) ps.length := by sorry
