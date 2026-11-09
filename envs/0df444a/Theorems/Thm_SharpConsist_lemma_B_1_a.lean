-- Prove2me | Theorems.Thm_SharpConsist_lemma_B_1_a
-- name    : SharpConsist.lemma_B_1_a
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:12:38.988333+00:00
-- url     : https://prove2.me/theorems/526959ed-5d55-476d-888e-f1c605ee8942
-- title:
--   Lemma B.1(a) — values and exact hiding
-- statement:
--   Fix $T\in[7/5,3/2]$ and an integer $m\ge32$, let $\delta=1/(64m)$, and let $F_\delta,K_\delta$ be the profiles of Eq. (5.5). On the rectangle $[0,1]\times[0,m]$:
--
--   1. $F_\delta(x,y)\ge0$ and $K_\delta(x,y)\ge0$;
--   2. $F_\delta(0,0)=0$;
--   3. if $|u|=|x-y/m|\le\delta$, then $F_\delta(x,y)=v(s)+\phi_m(s)$ with $s=x+y$.
--
--   Item 3 is the exact-hiding property: inside the balanced band the current branch depends only on the normalized size.
--
--   Differences from the source:
--   - encoding: v, w defined on [0, ∞) → v, w defined on ℝ by the quadratic/linear piece for t ≤ T; reason: every argument the statement evaluates is nonnegative (t = ω_m y ≥ 0, z between t and s ≥ 0)
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), Appendix B.2, Lemma B.1(a), p.34

import Mathlib
import Definitions.Def_SharpConsist_Fdelta

namespace SharpConsist

/-- **Lemma B.1(a) (values and exact hiding).** Fu–Zhang–Tao, *A Sharp Barrier of Consistent Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), Appendix B.2, Lemma B.1(a), p.34.
Fix `T ∈ [7/5, 3/2]` and an integer `m ≥ 32`. On the rectangle `[0, 1] × [0, m]` both profiles
`F_δ`, `K_δ` of Eq. (5.5) are nonnegative, `F_δ(0, 0) = 0`, and `F_δ(x, y) = v(s) + ϕ_m(s)`
(`s = x + y`) whenever `|u| = |x − y/m| ≤ δ`. -/
theorem lemma_B_1_a (T : ℝ) (hT : T ∈ Set.Icc (7 / 5 : ℝ) (3 / 2)) (m : ℕ) (hm : 32 ≤ m) :
    (∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) m →
      0 ≤ Fdelta T m x y ∧ 0 ≤ Kdelta T m x y) ∧
    Fdelta T m 0 0 = 0 ∧
    (∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) m →
      |x - y / (m : ℝ)| ≤ deltaM m → Fdelta T m x y = v T (x + y) + phiM m (x + y)) := by sorry

end SharpConsist
