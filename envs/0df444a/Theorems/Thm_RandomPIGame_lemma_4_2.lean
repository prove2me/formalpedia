-- Prove2me | Theorems.Thm_RandomPIGame_lemma_4_2
-- name    : RandomPIGame.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:24:35.568733+00:00
-- url     : https://prove2.me/theorems/29b5176d-6a72-46aa-842d-07bb9a0a8497
-- title:
--   Lemma 4.2: continuity, monotonicity, boundary values, shape and fixed points of $f_k$
-- statement:
--   Let $k\ge0$, and let $f_k$ be the value generating function of a primitive distribution $p$.
--
--   1. $f_k$ is continuous and non-decreasing on $[0,1]$, and differentiable any number of times at any point of $(0,1)$.
--   2. It holds that
--   $$
--   f_k(0)=p(\{\gamma<k\}),\qquad f_k(1)=p(\{\gamma<k\}\cup\{\xi\ge1\}),\qquad \lim_{x\uparrow1}\frac{\partial f_k}{\partial x}(x)=d(k).
--   $$
--   3. There exists a point $c\in[0,1]$ such that $f_k$ is concave on $[0,c]$ and convex on $[c,1]$.
--   4. Suppose that $f_k$ is not the identity map. If $s\in(0,1)$ is a fixed point of $f_k$, then $x<f_k(x)$ for each $x\in(0,s)$ and $f_k(x)<x$ for each $x\in(s,1)$. In particular, $f_k$ has at most one fixed point in $(0,1)$.
--   5. $f_k$ has no fixed point in $[0,1)$ if and only if $f_k(0)>0$, $f_k(1)=1$ and $d(k)\le1$.
--
--   Items 1 and 2 feed the fixed-point characterization of the value, and items 3 to 5 locate the fixed points.
--
--   Differences from the source:
--   - encoding: capacities and thresholds k in [0, ∞) → capacities and thresholds k in ℝ≥0; reason: Lean convention; the same numbers
--   - encoding: lim_{x↑1} ∂f_k/∂x(x) = d(k), a limit in [0, ∞] → Tendsto of ENNReal.ofReal (deriv (f p k) x) along 𝓝[<] 1 to d p k in ℝ≥0∞; reason: d(k) can be ∞; the derivative is nonnegative on (0, 1), so ENNReal.ofReal changes nothing
--   - encoding: f_k is not the identity map → ¬ Set.EqOn (f p k) id (Set.Icc 0 1); reason: f_k is a map on [0, 1]; the Lean function is on ℝ
--   - encoding: probabilities p(·) → Measure.real, a real number; reason: p is a probability measure, so nothing is lost
-- source:
--   Flesch, Predtetchinski & Suomala, Random perfect information games, arXiv:2104.10528v1, Lemma 4.2, p.13

import Mathlib
import Definitions.Def_RandomPIGame_Primitive

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace RandomPIGame

/-- Properties of the value generating function `f_k`, for `k ≥ 0`.
arXiv:2104.10528v1, Lemma 4.2, p.13.

1. `f_k` is continuous and non-decreasing on `[0, 1]`, and differentiable any number of times on
   `(0, 1)`.
2. `f_k(0) = p({γ < k})`, `f_k(1) = p({γ < k} ∪ {ξ ≥ 1})`, and `f_k'(x) → d(k)` as `x ↑ 1`.
3. There is `c ∈ [0, 1]` such that `f_k` is concave on `[0, c]` and convex on `[c, 1]`.
4. If `f_k` is not the identity on `[0, 1]` and `s ∈ (0, 1)` is a fixed point, then `x < f_k(x)` on
   `(0, s)` and `f_k(x) < x` on `(s, 1)`; in particular `f_k` has at most one fixed point in `(0, 1)`.
5. `f_k` has no fixed point in `[0, 1)` if and only if `f_k(0) > 0`, `f_k(1) = 1` and `d(k) ≤ 1`.

**Formalization Note.** `k ≥ 0` is the type `ℝ≥0`. The limit in item 2 is taken in `ℝ≥0∞`, since
`d(k)` can be `∞`; `f_k' ≥ 0` on `(0, 1)`, so `ENNReal.ofReal` loses nothing. -/
theorem lemma_4_2 (p : Measure S) [IsProbabilityMeasure p] (k : ℝ≥0) :
    (ContinuousOn (f p k) (Set.Icc 0 1) ∧ MonotoneOn (f p k) (Set.Icc 0 1) ∧
        ContDiffOn ℝ ∞ (f p k) (Set.Ioo 0 1)) ∧
      (f p k 0 = p.real {s : S | s.2.1 < k} ∧
        f p k 1 = p.real ({s : S | s.2.1 < k} ∪ {s : S | 1 ≤ s.2.2}) ∧
        Tendsto (fun x => ENNReal.ofReal (deriv (f p k) x)) (𝓝[<] 1) (𝓝 (d p k))) ∧
      (∃ c ∈ Set.Icc (0 : ℝ) 1,
        ConcaveOn ℝ (Set.Icc 0 c) (f p k) ∧ ConvexOn ℝ (Set.Icc c 1) (f p k)) ∧
      (¬ Set.EqOn (f p k) id (Set.Icc 0 1) →
        (∀ s ∈ Set.Ioo (0 : ℝ) 1, f p k s = s →
          (∀ x ∈ Set.Ioo 0 s, x < f p k x) ∧ ∀ x ∈ Set.Ioo s 1, f p k x < x) ∧
        {s ∈ Set.Ioo (0 : ℝ) 1 | f p k s = s}.Subsingleton) ∧
      ((¬ ∃ x ∈ Set.Ico (0 : ℝ) 1, f p k x = x) ↔ 0 < f p k 0 ∧ f p k 1 = 1 ∧ d p k ≤ 1) := by sorry

end RandomPIGame
