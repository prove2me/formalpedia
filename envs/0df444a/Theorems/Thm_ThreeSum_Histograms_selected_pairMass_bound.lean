-- Prove2me | Theorems.Thm_ThreeSum_Histograms_selected_pairMass_bound
-- name    : ThreeSum.Histograms.selected_pairMass_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:14:03.513205+00:00
-- url     : https://prove2.me/theorems/e0861d25-30fb-49eb-bfba-c6fff20a8754
-- title:
--   Histograms: selected pair Mass bound
-- statement:
--   The actual raw-incidence/output-key join obeys the exact balancing bound
--   for the selected offset, without an independent hash-uniformity premise.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Histograms.lean#L73-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Histograms.lean#L73-L83

import Definitions.Def_Submission_ThreeSum_Balancing
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Definitions.Def_Submission_ThreeSum_Histograms
set_option autoImplicit false
open ThreeSum ThreeSum.Histograms
open Finset
open scoped BigOperators
variable {ι τ ν G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem ThreeSum.Histograms.selected_pairMass_bound [Inhabited G]
    (keys : List G) (hkeys : ∀ d, d ∈ keys)
    (I : Finset ι) (J : Finset τ) (left : ι → G) (right : τ → G)
    (weightL : ι → ℕ) (weightR : τ → ℕ) :
    Fintype.card G * pairMass I J left right weightL weightR
      (Balancing.chooseOffset keys (histogram J right weightR) (histogram I left weightL)) ≤
        (∑ i ∈ I, weightL i) * (∑ j ∈ J, weightR j) := by sorry
