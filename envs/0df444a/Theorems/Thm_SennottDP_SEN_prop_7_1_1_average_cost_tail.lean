-- Prove2me | Theorems.Thm_SennottDP_SEN_prop_7_1_1_average_cost_tail
-- name    : SennottDP.SEN.prop_7_1_1_average_cost_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T10:17:50.517007+00:00
-- url     : https://prove2.me/theorems/4830f086-8825-4128-b720-655eed6a7466
-- title:
--   Proposition 7.1.1 — costs over finitely many initial transitions do not affect the average cost
-- statement:
--   Let $K$ be a positive integer, $i$ an initial state and $\theta$ a policy such that the $K$-horizon cost $v_{\theta,K}(i)$ is finite. Then the average cost can be computed from the costs incurred from time $K$ on:
--
--   $$J_\theta(i) = \limsup_{n\to\infty} \frac{1}{n-K}\, E_\theta\Big[\sum_{t=K}^{n-1} C(X_t,A_t) \,\Big|\, X_0 = i\Big]. \qquad (7.1)$$
--
--   The costs accumulated over any fixed finite number of transitions do not change the average cost, provided they are finite; the finiteness hypothesis cannot be dropped (Example 7.1.2).
--
--   **Formalization Note** The expectation of the sum is the sum over $K \le t < n$ of the expected costs, in `ℝ≥0∞`. For $n \le K$ the natural-number difference $n - K$ is $0$ and the quotient is a junk value; the limit supremum along $n \to \infty$ is unaffected.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 128, Proposition 7.1.1, (7.1)

import Mathlib
import Definitions.Def_SennottDP_SEN_Criteria

open scoped ENNReal NNReal
open Filter

namespace SennottDP.SEN

/-- Sennott (1999), Proposition 7.1.1, p. 128: let `K` be a positive integer, `i` an initial
state and `θ` a policy with `v_{θ,K}(i) < ∞`. Then
`J_θ(i) = limsup_{n→∞} (1/(n − K)) E_θ[∑_{t=K}^{n-1} C(X_t,A_t) | X_0 = i]` (7.1).
The expectation of the sum is the sum of the expected costs `E_θ[C(X_t,A_t) | X_0 = i]`,
`K ≤ t < n`; the terms with `n ≤ K` (where `n − K = 0` in `ℕ`) do not affect the limit supremum. -/
theorem prop_7_1_1_average_cost_tail {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act)
    (K : ℕ) (hK : 0 < K) (i : S) (θ : SennottDP.Discounted.Policy M) (hfin : horizonCost M θ K i < ⊤) :
    avgCost M θ i =
      limsup (fun n : ℕ => (∑ t ∈ Finset.Ico K n, SennottDP.Discounted.expCost M θ i t) / ((n - K : ℕ) : ℝ≥0∞))
        atTop := by sorry

end SennottDP.SEN
