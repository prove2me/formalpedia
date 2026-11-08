-- Prove2me | Theorems.Thm_RobustSPUA_theorem_7_tightening
-- name    : RobustSPUA.theorem_7_tightening
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T12:44:10.806645+00:00
-- url     : https://prove2.me/theorems/99464737-6489-4695-aec3-cd7f66c39490
-- title:
--   Proof of Theorem 7, p.33 — points satisfying (18)–(19) tighten into $\mathrm{POL}$ (corrected: recursion for $t\ge2$)
-- statement:
--   Fix $n\ge1$ and $p\in(0,1]$. Let $(x,y)\ge0$ satisfy the constraints (18)–(19):
--   $$
--   x_{1,1}+y_{1,1}\le1,\qquad x_{t,s}+y_{t,s}\le\frac1t\sum_{\sigma=1}^{t-1}\bigl(y_{t-1,\sigma}+(1-p)x_{t-1,\sigma}\bigr)\quad\forall t\in\{2,\dots,n\},\ s\in[t].
--   $$
--   Then there is $y'$ with $y'_{t,s}\ge y_{t,s}$ for all $t\in[n]$, $s\in[t]$, such that $(x,y')\in\mathrm{POL}$.
--
--   Since the objective of (9) does not depend on $y$, this shows that relaxing the equalities of POL to the inequalities (18)–(19) does not change the optimal value: $\gamma^*_n$ is the value of $(P')$.
--
--   **Formalization Note** The point keeps $x'=x$; "the objective of $\gamma$ is the same for both points" is then automatic, since the objective depends on $x$ only.
--
--   Differences from the source:
--   - correction: (19) and POL with the recursion for all t ∈ [n] (pp.29, 30) → both with the recursion for t ∈ [2, n]; reason: as printed the claim fails: x = y = 0 satisfies the printed (18)–(19), but the printed POL is empty (its t = 1 row forces x_{1,1}+y_{1,1} = 0 against = 1)
--   - reading: a point (x, y) satisfying (18)–(19) → such a point with (x, y) ≥ 0; reason: (18)–(19) are the constraints of (P), p.29, which maximizes over x, y ≥ 0; without y ≥ 0 the claim fails: n = 1, x_{1,1} = 2, y_{1,1} = −1 satisfies (18), and no y′ ≥ 0 has x_{1,1}+y′_{1,1} = 1
--   - encoding: the number of candidates n, implicitly positive (the min over k ∈ [n] in (1) and the initial state (1,1) need it) → the explicit hypothesis 1 ≤ n; reason: a nondegeneracy condition that only excludes the undefined case n = 0
--   - encoding: vectors x, y and policies indexed by the states (t,s), t ∈ [n], s ∈ [t] → total real-valued functions of two natural numbers; reason: only the values at the states are constrained or read, so the instances are the same
-- source:
--   Perez-Salazar, Singh, Toriello, Robust Online Selection with Uncertain Offer Acceptance, arXiv:2112.00842v2, proof of Theorem 7, p.33 (constraints (18)–(19) of (P), p.29)

import Mathlib
import Definitions.Def_RobustSPUA_Model
import Definitions.Def_RobustSPUA_LP

open Finset

namespace RobustSPUA

/-- S. Perez-Salazar, M. Singh, A. Toriello, *Robust Online Selection with Uncertain Offer Acceptance*, arXiv:2112.00842v2, proof of Theorem 7, p.33 (corrected: recursion for `t ≥ 2`): any point `(x, y)`
satisfying the constraints (18)–(19) has an equivalent point `(x, y′) ∈ POL` with `y′ ≥ y`.

**Formalization Note** (19) and POL are read with the recursion for `t ∈ [2, n]`; as printed
(`∀ t ∈ [n]`) the point `x = y = 0` satisfies (18)–(19) while the printed POL is empty. -/
theorem theorem_7_tightening (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (x y : ℕ → ℕ → ℝ) (hxy : POLineq n p x y) :
    ∃ y' : ℕ → ℕ → ℝ, (∀ t ∈ Icc 1 n, ∀ s ∈ Icc 1 t, y t s ≤ y' t s) ∧ POL n p x y' := by sorry

end RobustSPUA
