-- Prove2me | Theorems.Thm_WasteNotWant_benchmark_optimal
-- name    : WasteNotWant.benchmark_optimal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:41.700316+00:00
-- url     : https://prove2.me/theorems/8d863c59-90b0-4960-93ff-cfeca4f24301
-- title:
--   The benchmark optimum: $F(q^B/(1-p_f))=1-(c_m+c)/p_f$ and $x^B=q^B$
-- statement:
--   Let $\mu$ be a market law on $[a,b]$ with cdf $F$. A pair $(x,q)$ is optimal in the benchmark model if and only if
--   $$F\Bigl(\frac{q}{1-p_f}\Bigr)=1-\frac{c_m+c}{p_f}\qquad\text{and}\qquad x=q,$$
--   and an optimal pair exists.
--
--   The firm buys exactly the fabric it uses, and the production level is the classical newsvendor critical fractile. This is the reference point for every comparison in the mission.
--
--   Differences from the source:
--   - reading: market size with cdf F on support [a, b] → law μ with cdf F = cdf μ: probability measure carried by [a, b], positive on every open subinterval, no atoms, 0 ≤ a < b; reason: the fractile equations with levels in (0, 1) presuppose a continuous, strictly increasing F; Y is a number of consumers, and a = b would be an atom
--   - reading: p_f > c + c_m → p_f > c + c_m together with p_f < 1, c_m > 0, c ≥ 0; reason: valuations are uniform on [0, 1] and the paper divides by 1 − p_f; c and c_m are unit costs; at c_m = 0 the optimal fabric level is not unique
--   - reading: maximize subject to q ≤ x → maximize over the set 0 ≤ q ≤ x; reason: the proof on p.44 states the constraints q ≤ x, q ≥ 0, x ≥ 0
--   - reading: the optimal decisions are given by the displayed equations → a pair is optimal if and only if the equations hold, and an optimal pair exists; reason: the equations have exactly one solution under the reading of the law, so this is what the printed sentence asserts
-- source:
--   Long–Gui, Waste Not Want Not?, SSRN 4013877 (2023-08-10 copy), §3.1, p.10

import Mathlib
import Definitions.Def_WasteNotWant_Model

open MeasureTheory ProbabilityTheory

namespace WasteNotWant

/-- **The optimal decisions of the benchmark model.**
Long–Gui, *Waste Not Want Not?*, SSRN 4013877 (2023-08-10 copy), §3.1, p.10: the optimal decisions
`(x^B, q^B)` are given by `F(q^B / (1 - p_f)) = 1 - (c_m + c) / p_f` and `x^B = q^B`.

**Formalization Note.** "Are given by" is read as: `(x, q)` is optimal if and only if the two
equations hold, and an optimal pair exists. `q^B_δ = 0` is part of the model (the benchmark has no
stage-2 decision), so it is not a claim here. -/
theorem benchmark_optimal (P : Params) {μ : Measure ℝ} {a b : ℝ} (hμ : IsMarketLaw μ a b) :
    (∀ x q : ℝ, IsBenchmarkOptimal P μ x q ↔
      cdf μ (q / (1 - P.pf)) = 1 - (P.cm + P.c) / P.pf ∧ x = q) ∧
    ∃ x q : ℝ, IsBenchmarkOptimal P μ x q := by sorry

end WasteNotWant
