-- Prove2me | Theorems.Thm_ThreeSum_Histograms_correlation_histograms_w3sum_ac885d1
-- name    : ThreeSum.Histograms.correlation_histograms_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:14:05.694035+00:00
-- url     : https://prove2.me/theorems/052f48f0-89aa-4580-a537-4d3e730e5fe0
-- title:
--   Histograms: correlation histograms
-- statement:
--   The Histograms construction uses the correlation histograms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Histograms.lean#L37-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Histograms.lean#L37-L62

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

theorem ThreeSum.Histograms.correlation_histograms_w3sum_ac885d1 (I : Finset ι) (J : Finset τ)
    (left : ι → G) (right : τ → G) (weightL : ι → ℕ) (weightR : τ → ℕ) (d : G) :
    Balancing.correlation (histogram J right weightR) (histogram I left weightL) d =
      pairMass I J left right weightL weightR d := by sorry
