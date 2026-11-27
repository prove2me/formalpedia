-- Prove2me | Theorems.Thm_ShipConsol_OneWH_Supplement_theorem_6
-- name    : ShipConsol.OneWH.Supplement.theorem_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T06:32:26.558077+00:00
-- url     : https://prove2.me/theorems/9a0f9156-6fa5-4155-94b3-9c0e89919056
-- title:
--   Theorem 6 (corrected: finite-T counterexample) — failure already at zero variable cost
-- statement:
--   The printed finite-T comparison is false even with Bernoulli arrivals. Take T=5, d=3, α=3/4, γ=0, and
--
--   $$F(x)=\max\{2,4-x\},\qquad v(x)=0.$$
--
--   All cost and arrival assumptions hold. Threshold τ=2 minimizes the fixed-cost limiting criterion of Theorem 2. Exact H3 expected total costs at thresholds 1,2,3 are 519/128, 471/128 and 6. An admissible H2 policy with threshold 3 at t=1, threshold 2 when t≥3 and threshold 1 otherwise has total cost 459/128. Consequently, with the unrestricted optimal expected average C*,
--
--   $$0<C^*,\qquad\frac{\widetilde C-C^*}{C^*}>\min\left\{\frac{\gamma(d-\tau)\alpha}{1+\gamma},\frac{d\alpha}{\gamma(1+d\alpha)+1}\right\}=0.$$
--
--   The witness gives relative gap at least 4/153. No ratio is evaluated at a zero benchmark, and both printed denominators are positive at γ=0. The example refutes the finite-T universal claim on an allowed instance; it does not introduce a Bernoulli restriction into a replacement universal theorem.
--
--   Differences from the source:
--   - correction: Theorem 6 asserts both finite-T relative bounds for γ≥0 and general bounded batches → an explicit Bernoulli counterexample at γ=0, with a fixed-cost minimizing τ=2; reason: 471/128>459/128, whereas the printed first bound is zero; PDF25 includes γ=0, and OA13 replaces finite-T costs by cycle formulas; see DISPROOF.md
--   - encoding: unrestricted optimal expected average cost → the value of the unrestricted subset-and-partition Bellman recursion divided by T; reason: the H2 witness is admissible in this full optimization, so the optimum is at most its evaluated cost
-- source:
--   Wei, Kapuscinski & Jasin, Shipping Consolidation across Two Warehouses with Delivery Deadline and Expedited Options for E-commerce and Omni-channel Retailers, author's manuscript, SSRN 2920899 (M&SOM 2020, doi:10.1287/msom.2020.0903), pinned PDF sha256 2cc7647135cddd3db3d07ad21c65ac52502947d2dde5f337f3ab9948547f0a03, Theorem 6, p. 25; proof OA12–OA13 (PDF44–45)

import Mathlib
import Definitions.Def_ShipConsol_OneWH_Supplement_Variable

namespace ShipConsol.OneWH.Supplement

/-- The printed first bound is zero at γ=0, but finite-horizon constant thresholds
can be strictly suboptimal. This example already has Bernoulli arrivals. -/
theorem theorem_6 :
    example6.SourceData ∧
    (∀ x, example6.v x = (0 : ℝ) * example6.F x) ∧
    fixedMinimizer example6 2 ∧
    h3Total example6 5 1 = 519 / 128 ∧
    h3Total example6 5 2 = 471 / 128 ∧
    h3Total example6 5 3 = 6 ∧
    validThresholds 3 witnessThreshold6 ∧
    h2Total example6 5 witnessThreshold6 = 459 / 128 ∧
    0 < optimalAverage example6 5 ∧
    (h3Average example6 5 - optimalAverage example6 5) / optimalAverage example6 5 >
      bound6 3 2 (3 / 4) 0 := by sorry

end ShipConsol.OneWH.Supplement
