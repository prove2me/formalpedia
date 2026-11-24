-- Prove2me | Theorems.Thm_ShipConsol_OneWH_Supplement_theorem_2
-- name    : ShipConsol.OneWH.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:28:32.431196+00:00
-- url     : https://prove2.me/theorems/87bd2ce1-8433-4fa9-9252-b4e619c048aa
-- title:
--   Theorem 2 — exact expected average cost limit of a constant threshold
-- statement:
--   Let d≥1 and 1≤τ≤d be integers. Let F be a nonnegative, convex, non-increasing shipping cost on [1,∞), and let α∈[0,1] be the independent probability of a nonempty arrival batch. Evaluate the constant-threshold policy from an empty system over T periods, including forced terminal shipment, and write A_T^τ for its expected average cost. Then
--
--   $$\lim_{T\to\infty}A_T^\tau=G_\tau(\alpha,d),\qquad G_\tau(\alpha,d)=\frac{F(\tau)}{1/\alpha+d-\tau}\quad(\alpha>0),$$
--
--   with G_τ(0,d)=0. The result gives the exact limiting cost of every feasible fixed threshold; no rate or finite-T equality is asserted.
--
--   Differences from the source:
--   - encoding: bounded batches with nonempty-arrival probability α → independent nonempty-arrival indicators; reason: fixed shipping cost and minimum-slack evolution are independent of the positive batch size
--   - reading: printed reciprocal expression at α=0 → zero expected average cost and zero limiting criterion at α=0; reason: the initially empty no-arrival process is identically empty; this is the continuous extension, not real division by zero
--   - encoding: average cost over a sufficiently long horizon → Tendsto of actual finite-horizon expected costs with terminal flush; reason: the terminal convention is DP (1), p. 11, and has a vanishing contribution to the limit
-- source:
--   Wei, Kapuscinski & Jasin, Shipping Consolidation across Two Warehouses with Delivery Deadline and Expedited Options for E-commerce and Omni-channel Retailers, author's manuscript, SSRN 2920899 (M&SOM 2020, doi:10.1287/msom.2020.0903), pinned PDF sha256 2cc7647135cddd3db3d07ad21c65ac52502947d2dde5f337f3ab9948547f0a03, Theorem 2, p. 14; proof OA2 (PDF34)

import Mathlib
import Definitions.Def_ShipConsol_OneWH_Supplement_FixedRun

namespace ShipConsol.OneWH.Supplement

theorem theorem_2 (F : ℝ → ℝ) (hF : CostAssumptions F)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (d τ : ℕ) (hd : 1 ≤ d) (hτ : 1 ≤ τ ∧ τ ≤ d) :
    Filter.Tendsto (fun T : ℕ => fixedExpectedAverage F α d τ T)
      Filter.atTop (nhds (fixedCriterion F α d τ)) := by sorry

end ShipConsol.OneWH.Supplement
