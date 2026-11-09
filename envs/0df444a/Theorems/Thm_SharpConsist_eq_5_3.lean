-- Prove2me | Theorems.Thm_SharpConsist_eq_5_3
-- name    : SharpConsist.eq_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:10:56.846426+00:00
-- url     : https://prove2.me/theorems/5e430e50-741e-439c-9545-359125e93339
-- title:
--   Eq. (5.3) and the identities of §5.1
-- statement:
--   Fix $T\in[7/5,3/2]$ and an integer $m\ge32$, and let $v,w,c,d$ be as in Eq. (5.2) and $R(T)=(T^2+2)/(T^2+2T+2)$. Then:
--
--   1. $1-c=d(T+1)$ and $c=dT^2/2$;
--   2. for $t\ge0$, $w(t)-v(t)=\frac d2\,(T-t)_+^2$;
--   3. $c+v'(0)=1$;
--   4. $w(1)=d+c=R(T)$;
--   5. $$R(T)-(2-\sqrt2)=\frac{(\sqrt2-1)(T-\sqrt2)^2}{T^2+2T+2};$$
--   6. $v$ and $w$ are nondecreasing and concave on $[0,\infty)$;
--   7. $v$ is of class $C^2$, and $w$ is of class $C^1$ with locally Lipschitz derivative.
--
--   These identities give tangential contact of the two profiles at $T$, the balanced value $w(1)=R(T)$ and the hidden-complement value $c+v'(0)=1$; item 5 shows that $R$ is minimized at $T=\sqrt2$.
--
--   **Formalization Note.** $v,w$ are extended to $\mathbb R$ by their first pieces, and item 7 is stated on $\mathbb R$.
--
--   Differences from the source:
--   - encoding: v, w defined on [0, ∞) → v, w defined on ℝ by the quadratic/linear piece for t ≤ T; reason: every argument the statement evaluates is nonnegative (t = ω_m y ≥ 0, z between t and s ≥ 0)
--   - generalization: v of class C² and w of class C¹ with locally Lipschitz derivative (on [0, ∞)) → ContDiff ℝ 2 (v T), ContDiff ℝ 1 (w T) and LocallyLipschitz (deriv (w T)) on all of ℝ for the extended profiles; reason: restricting to [0, ∞) gives the source's claim
--   - encoding: v′, the derivative of v → v', the explicit piecewise formula d(T + 1 − t) for t ≤ T and d·e^{−(t−T)} for t > T; reason: it is the derivative of v at every real t (both pieces agree at t = T), so v′(0) = d(T + 1) as in the source
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.1, Eq. (5.3), p.13

import Mathlib
import Definitions.Def_SharpConsist_v
import Definitions.Def_SharpConsist_RT

namespace SharpConsist

/-- **Eq. (5.3) and the identities of §5.1.** Fu–Zhang–Tao, *A Sharp Barrier of Consistent Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.1, p.13.
For `T ∈ [7/5, 3/2]`: `1 − c = d(T + 1)`, `c = dT²/2`; `w(t) − v(t) = (d/2)(T − t)₊²` for `t ≥ 0`;
`c + v′(0) = 1`; `w(1) = d + c = R(T)`; `R(T) − (2 − √2) = (√2 − 1)(T − √2)²/(T² + 2T + 2)`;
`v` and `w` are nondecreasing and concave on `[0, ∞)`; `v` is `C²` and `w` is `C¹` with locally
Lipschitz derivative.

**Formalization Note.** `v`, `w` are defined on all of `ℝ` (quadratic/linear piece for `t ≤ T`);
the regularity clauses are stated on `ℝ`, which contains the paper's `[0, ∞)`. -/
theorem eq_5_3 (T : ℝ) (hT : T ∈ Set.Icc (7 / 5 : ℝ) (3 / 2)) :
    1 - cT T = dT T * (T + 1) ∧ cT T = dT T * T ^ 2 / 2 ∧
    (∀ t : ℝ, 0 ≤ t → w T t - v T t = dT T / 2 * (max (T - t) 0) ^ 2) ∧
    cT T + v' T 0 = 1 ∧
    w T 1 = dT T + cT T ∧ RT T = w T 1 ∧
    RT T - (2 - Real.sqrt 2) = (Real.sqrt 2 - 1) * (T - Real.sqrt 2) ^ 2 / (T ^ 2 + 2 * T + 2) ∧
    MonotoneOn (v T) (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) (v T) ∧
    MonotoneOn (w T) (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) (w T) ∧
    ContDiff ℝ 2 (v T) ∧ ContDiff ℝ 1 (w T) ∧ LocallyLipschitz (deriv (w T)) := by sorry

end SharpConsist
