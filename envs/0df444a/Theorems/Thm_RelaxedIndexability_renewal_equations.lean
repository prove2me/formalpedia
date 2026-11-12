-- Prove2me | Theorems.Thm_RelaxedIndexability_renewal_equations
-- name    : RelaxedIndexability.renewal_equations
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:20:57.90435+00:00
-- url     : https://prove2.me/theorems/6c15f254-1af5-4e8d-88b0-8a2d820dcde2
-- title:
--   (35)–(36) — renewal equations of the threshold policy at the rows $p_k$ (corrected: $\mathcal T^{L}(p_k)$ for $\mathcal T^{L}(\omega)$ in (36))
-- statement:
--   Let an arm have $K$ states, a row-stochastic transition matrix $\mathbf P$ with rows $p_0,\dots,p_{K-1}$ and rewards $B$, let $0 < \beta < 1$, let $\omega$ be a belief fixed as a point in the threshold and $m$ a subsidy. Write $\hat V_{\beta,m}$ for the value of the threshold policy $\pi_{\beta,m}$ and $L(p_k,\omega)$ for the first-crossing time (34). For every $k \in \{0, \dots, K-1\}$:
--
--   1. if $L(p_k, \omega) = n$ is finite, then
--   $$
--   \hat V_{\beta,m}(p_k) = \frac{1-\beta^{n}}{1-\beta}\, m + \beta^{n}\, \hat V_{\beta,m}\big(\mathcal T^{n}(p_k); u=1\big),
--   $$
--   $$
--   \hat V_{\beta,m}\big(\mathcal T^{n}(p_k); u=1\big) = \mathcal T^{n}(p_k) B' + \beta\, \mathcal T^{n}(p_k)\big(\hat V_{\beta,m}(p_0), \dots, \hat V_{\beta,m}(p_{K-1})\big)',
--   $$
--   where $\mathcal T^{n}(p_k) = p_k \mathbf P^{n}$;
--   2. if $L(p_k,\omega) = +\infty$, then $\hat V_{\beta,m}(p_k) = m/(1-\beta)$.
--
--   Started at $p_k$, the threshold policy collects the subsidy for $L(p_k,\omega)$ passive slots and is then active. These equations reduce the value of the policy at the $K$ rows of $\mathbf P$ to a linear system (Lemma 3), from which the approximated Whittle index (41) is computed.
--
--   Differences from the source:
--   - correction: (36) has βT^{L(p_k,ω)}(ω)(V̂(p₀),…,V̂(p_{K−1}))′ as its last term → βT^{L(p_k,ω)}(p_k)(V̂(p₀),…,V̂(p_{K−1}))′; reason: activating at belief T^{L}(p_k) leads to p_j with probability T^{L}(p_k)_j. Counterexample to the printed form: K = 2, P = [[1/2,1/2],[1/5,4/5]] (irreducible, aperiodic), B = (0,1), β = 1/2, ω = (1,0); then L(p₀,ω) = L(p₁,ω) = 0, (V̂(p₀),V̂(p₁)) = (20/17, 26/17), and the printed right side for k = 0 is 1/2 + (1/2)(20/17) = 37/34 ≠ 20/17. The proof (EC.38, p.ec9) and g (p.23) use the corrected form.
--   - reading: (35)–(36) with L(p_k,ω) = +∞ → V̂(p_k) = m/(1−β), and (36) is not stated for that k; reason: β^{+∞} = lim βⁿ = 0 (also Algorithm 1), and T^{+∞}(p_k) is not a belief.
--   - generalization: the standing assumptions P irreducible and aperiodic (footnote, p.7) and 0 = B₀ ≤ ⋯ ≤ B_{K−1} (p.11) → not assumed; reason: they serve only the stationary initial belief (3) and a normalization; the statement for every row-stochastic P and every B contains the source's case.
--   - encoding: V̂ is the expected total discounted reward of π_{β,m} → the limit of the n-horizon expected discounted rewards computed by conditioning on the observations (4); reason: the same quantity, the limit exists for 0 < β < 1.
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, (35)–(36), p.20; proof of Lemma 3, (EC.38), p.ec9

import Mathlib
import Definitions.Def_RelaxedIndexability_crossTime
import Definitions.Def_RelaxedIndexability_thresholdValue

open Matrix

namespace RelaxedIndexability

/-- **Renewal equations (35)–(36) for the threshold policy** (Liu, *Relaxed Indexability and Index
Policy for Partially Observable Restless Bandits*, arXiv:2107.11939v4, (35)–(36), p.20; `(36)`
corrected). Fix a threshold belief `ω` and a subsidy `m`. Started at the row `p_k`, the threshold
policy stays passive for `L(p_k, ω)` slots and then becomes active at `T^{L}(p_k) = p_k P^{L}`:

* if `L(p_k, ω) = n` is finite, `V̂(p_k) = (1 − βⁿ)/(1 − β) m + βⁿ V̂(p_k Pⁿ; u = 1)` and
  `V̂(p_k Pⁿ; u = 1) = p_k Pⁿ B′ + β p_k Pⁿ (V̂(p₀), …, V̂(p_{K−1}))′`;
* if `L(p_k, ω) = +∞`, `V̂(p_k) = m/(1 − β)`.

**Formalization Note.** The page prints `T^{L(p_k,ω)}(ω)` in the second term of (36); the
correct belief is `T^{L(p_k,ω)}(p_k)` (counterexample: `K = 2`, `P = [[1/2,1/2],[1/5,4/5]]`,
`B = (0,1)`, `β = 1/2`, `ω = (1,0)`). The case `L = +∞` is (35) with `β^{+∞} = 0`. -/
theorem renewal_equations {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K)) (B : Fin K → ℝ)
    (ω : Fin K → ℝ) (hω : ω ∈ stdSimplex ℝ (Fin K)) (m : ℝ) (k : Fin K) :
    (∀ n : ℕ, crossTime P B ω (P k) = n →
      thresholdValue β P B ω m (P k) =
          (1 - β ^ n) / (1 - β) * m
            + β ^ n * thresholdActionValue β P B ω m true (P k ᵥ* P ^ n) ∧
      thresholdActionValue β P B ω m true (P k ᵥ* P ^ n) =
          (P k ᵥ* P ^ n) ⬝ᵥ B
            + β * ((P k ᵥ* P ^ n) ⬝ᵥ fun j => thresholdValue β P B ω m (P j))) ∧
    (crossTime P B ω (P k) = ⊤ → thresholdValue β P B ω m (P k) = m / (1 - β)) := by sorry

end RelaxedIndexability
