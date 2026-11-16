-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_Supplement_theorem_b_4
-- name    : SampleCRS.AlmostGreedy.Supplement.theorem_b_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:45:50.528143+00:00
-- url     : https://prove2.me/theorems/e3472860-972c-4770-b5af-c879533e0481
-- title:
--   Theorem B.4 — Conservative Scaling at every capacity
-- statement:
--   For every capacity $k\ge1$, Algorithm 6 (Conservative Scaling) is a single-sample random-order contention resolution scheme with
--   $$C_i\ge\gamma_k=1-e^{-k}k^k/k!\qquad(p_i>0)$$
--   on every unknown $p\in[0,1]^n$ with $\sum_i p_i\le k$. Every realization outputs an active subset of size at most $k$. The experiment averages independent uniform order, activations, sample bits and per-element thinning coins. Its coin bias is exactly $\alpha_k=\gamma_k/E[\operatorname{AR}_k(\operatorname{Poi}(k-1))]$, depends only on $k$, and is a valid probability; its denominator is strictly positive. At $k=1$ the denominator is one and this is Algorithm 1.
--
--   The full polytope domain follows the balanced-ROCRS convention of §2 and the extension in Appendix C.5, without altering the published goal's exact-mass statement.
--
--   Differences from the source:
--   - encoding: elements 1,…,n and independent Bernoulli trials → Fin n and finite product-weight expectations; reason: the label shift is a bijection and the weights are exactly the independent Bernoulli law
--   - encoding: Algorithm 6 uses the coin bias α_k=γ_k/δ_k and is a γ_k-balanced ROCRS → the same defined run, with δ_k>0 and α_k∈[0,1] also asserted; reason: these well-definedness properties are necessary to the stated Bernoulli algorithm, and are proved rather than imposed as extra assumptions
--   - encoding: balancedness for the polytope P_k under §2 and Remark 2.1 → all vectors of total mass at most k; reason: Appendix C.5 explicitly extends the equality-mass proof to this full domain by monotonicity and dummy elements
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Theorem B.4, p. 42

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_scaling

namespace SampleCRS.AlmostGreedy.Supplement

/-- Theorem B.4, p.42. Conservative Scaling at every capacity. -/
theorem theorem_b_4 (k : ℕ) (hk : 1 ≤ k) :
    0 < deltaScale k ∧ alphaScale k ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ (n : ℕ) (p : Fin n → ℝ), ValidProb p → (∑ i, p i) ≤ (k : ℝ) →
      ScalingFeasible n k ∧ ∀ i, 0 < p i →
        StaticProphetSec.gamma k ≤ scalingC k (alphaScale k) p i := by sorry

end SampleCRS.AlmostGreedy.Supplement
