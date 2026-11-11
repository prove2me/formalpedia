-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_optimal_moment_sample_complexity
-- name    : SingleCopyMoments.Adaptive.optimal_moment_sample_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:46:21.228563+00:00
-- url     : https://prove2.me/theorems/3d34bbc7-e230-44c4-b8c5-996b9ce6e251
-- title:
--   Theorem 1 — Optimal adaptive estimation of every integer state moment
-- statement:
--   For every fixed integer $t\ge2$, let $h=\lceil\log_2t\rceil$. There is a positive dimension-independent threshold $\varepsilon_t$ such that for every fixed $0<\varepsilon\le\varepsilon_t$ there are constants $c,C>0$ and $d_0\ge1$ with the following two conclusions for every $d\ge d_0$.
--
--   One randomized adaptive single-copy protocol, chosen before the state, has a natural fixed worst-case budget $T$ with
--
--   $$T\le Cd^{h/(h+1)},\qquad\Pr_\rho\{|\widehat p_t-\operatorname{Tr}(\rho^t)|\le\varepsilon\}\ge2/3\quad\text{for every density matrix }\rho.$$
--
--   Conversely, every admissible protocol with that uniform success guarantee has
--
--   $$cd^{h/(h+1)}\le T.$$
--
--   The constants may depend on $t$ and the fixed error, never on dimension, state, or strategy. Every rank and every density matrix on $\mathbb C^d$ is included. POVMs may have arbitrary measurable outcome spaces, including continuous ones, and measurements may adapt to all past classical outcomes and the input-independent seed. Only classical information passes between copies. Pilot copies, failed filters and padding are charged to the fixed budget.
--
--   This is both directions of the optimal worst-case complexity claim. In particular, the third and fourth moments share exponent $2/3$, and every order five through eight has exponent $3/4$.
--
--   Differences from the source:
--   - encoding: finite-dimensional states, measurable experiments, and their expectations → complex Fin d matrices, explicit Born/product measures, and normalized measurable operations; reason: the coordinate and measure conventions preserve every positive dimension and arbitrary rank; probability and integrability assertions are conclusions, not extra premises
--   - encoding: Theta of d to the dyadic exponent at sufficiently small fixed error → a positive error threshold followed by both operational bounds, with constants before dimension, states, and strategies; reason: this is the source Section 5 asymptotic convention and the all-smaller-errors conclusion of Theorem 30; no infimum or oracle complexity predicate is used
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Theorem 1, printed p. 2 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf; PDF SHA-256 f19fd65f41a444a79243fa55aab5dfca3db6adb571b06acff78ee49932174fa9.

import Definitions.Def_SingleCopyMoments_Adaptive_Estimation

open scoped Matrix.Norms.L2Operator

open scoped ENNReal

namespace SingleCopyMoments.Adaptive

/-- Liu, STOC 2027 submission #41 (October 2026), Theorem 1, printed p.2 (PDF p.4).
The constants and the positive small-error threshold precede the dimension, state, and protocol. -/
theorem optimal_moment_sample_complexity (t : ℕ) (ht : 2 ≤ t) :
    ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ c > 0, ∃ C > 0, ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        (∃ T : ℕ, ∃ P : Protocol d,
          (T : ℝ) ≤ C * (d : ℝ) ^ exponent t ∧ AdditiveSucceeds P T t ε (1/3)) ∧
        (∀ T : ℕ, ∀ P : Protocol d, AdditiveSucceeds P T t ε (1/3) →
          c * (d : ℝ) ^ exponent t ≤ (T : ℝ)) := by sorry

end SingleCopyMoments.Adaptive
