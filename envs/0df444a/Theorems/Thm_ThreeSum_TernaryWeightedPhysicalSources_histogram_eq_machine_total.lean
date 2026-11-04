-- Prove2me | Theorems.Thm_ThreeSum_TernaryWeightedPhysicalSources_histogram_eq_machine_total
-- name    : ThreeSum.TernaryWeightedPhysicalSources.histogram_eq_machine_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:50:40.654211+00:00
-- url     : https://prove2.me/theorems/1c54c54c-1a33-441d-bb4c-8fe923d0c561
-- title:
--   Ternary Weighted Physical Sources: histogram eq machine total
-- statement:
--   The physical weighted loop has exactly the histogram semantics when
--   its compact enumeration is injective on the bank.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightedPhysicalSources.lean#L91-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightedPhysicalSources.lean#L91-L103

import Definitions.Def_Submission_ThreeSum_TernaryPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWeightedPhysicalSources
open Finset TernaryJointType TernaryBank TernaryConvolution
open scoped BigOperators
variable {ι κ : Type*}

theorem ThreeSum.TernaryWeightedPhysicalSources.histogram_eq_machine_total {N bank n r : ℕ}
    (enumeration : ℕ → TritWord N) (key : ℕ → ℕ) (weight : ℕ → ℤ)
    (hr : r < bank) (hkey : ∀ j < n, key j < bank)
    (hinj : ∀ i j, i < bank → j < bank → enumeration i=enumeration j → i=j) :
    histogram (range n) (fun i => enumeration (key i)) weight (enumeration r)=
      LightTernaryWeightedHistogram.total key weight r n := by sorry
