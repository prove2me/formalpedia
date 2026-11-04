-- Prove2me | Theorems.Thm_ThreeSum_TernarySourceHostModel_read_physical
-- name    : ThreeSum.TernarySourceHostModel.read_physical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:26.394072+00:00
-- url     : https://prove2.me/theorems/861d2ef3-9802-4626-a295-631845e02c4f
-- title:
--   Ternary Source Host Model: read physical
-- statement:
--   The returned physical join list may use any order. Every emitted compact
--   histogram cell nevertheless denotes the same fixed set of original records.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostModel.lean#L95-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostModel.lean#L95-L112

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

theorem ThreeSum.TernarySourceHostModel.read_physical (M NL NR bank groups valueBase factor : ℕ)
    (input dictionary : ℕ → ℤ) (enumeration : ℕ → TritWord N)
    (key group : ℕ → ℕ) (weight : ℕ → ℤ) (ν : ℕ → ℤ)
    (ps : List (ℕ × ℕ)) (hn : ps.Nodup)
    (hmem : ∀ i j, (i,j)∈ps ↔ i<NL ∧ j<NR ∧ (M : ℤ)∣input i-dictionary j)
    (hkey : ∀ j<NR, key j<bank)
    (hinj : ∀ i j, i<bank → j<bank → enumeration i=enumeration j → i=j)
    (hread : ∀ r<groups*bank, ν (valueBase+r)=(factor : ℤ)*
      LightTernaryWeightedHistogram.total
        (fun i => group (ps.getD i (0,0)).2*bank+key (ps.getD i (0,0)).2)
        (fun i => weight (ps.getD i (0,0)).1) r ps.length) :
    ∀ g<groups, ∀ r<bank, ν (valueBase+g*bank+r)=(factor : ℤ)*
      physical (records M NL NR input dictionary) enumeration key group weight g (enumeration r) := by sorry
