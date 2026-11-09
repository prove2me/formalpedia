-- Prove2me | Theorems.Thm_SecondBestTrade_HalfEfficiency_half_first_best
-- name    : SecondBestTrade.HalfEfficiency.half_first_best
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:58.754193+00:00
-- url     : https://prove2.me/theorems/a2d775b7-fe07-4e1d-9609-a5ac013f17d5
-- title:
--   Theorem 1.1 — Main theorem
-- statement:
--   In every multidimensional two-sided market with the stated finite supports, independent agents, arbitrary within-agent correlation and arbitrary nonempty downward-closed feasibility family, there exists a direct mechanism with nonnegative buyer payments and seller receipts that is Bayesian incentive compatible, interim individually rational and strongly budget balanced at every report profile, such that
--   $$\mathrm{GFT}(x)\ge\tfrac12\mathrm{FB}.$$
--   The equivalent benchmark conclusion is retained:
--   $$\mathrm{SB}\ge\tfrac12\mathrm{FB}.$$
--   The witness is an actual admissible mechanism. The theorem includes zero gains from trade, empty trade sets and isolated agents; it imposes no item-independence, regularity, scalar-type, matching or positive-FB restriction.
--
--   This is the full existential guarantee of Theorem 1.1, rather than only an inequality for a relaxed or dual benchmark.
--
--   Differences from the source:
--   - encoding: finite agent, trade and support sets with product-prior expectations → Fin labels, an injective nonnegative-vector support embedding, and finite product-weighted sums; reason: bijections cover every finite source market, and summing an overwritten own coordinate multiplies by its total probability one
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), Theorem 1.1 — Main theorem, printed p. 2 (PDF p. 3)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_Mechanisms

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Theorem 1.1, printed p. 2 (PDF p. 3). -/
theorem half_first_best (N : Market) :
    (∃ m : Mechanism N, admissible N m ∧ (1 / 2 : ℝ) * FB N ≤ GFT N m.x) ∧
    (1 / 2 : ℝ) * FB N ≤ SB N := by sorry

end SecondBestTrade.HalfEfficiency
