-- Prove2me | Theorems.Thm_QuantumTriangleFinding_Search_moving_difference_average
-- name    : QuantumTriangleFinding.Search.moving_difference_average
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:27:06.133888+00:00
-- url     : https://prove2.me/theorems/2aaddfd6-3821-4286-9696-8ae06273a777
-- title:
--   Lemma 4.6 — Moving a difference through an averaging operator
-- statement:
--   Use the forbidden-pattern law $\mu$ with $0<p\le1/2$. Let $H=\sum_jw_jD_j$, with $w_j\ge0$ and $\sum_jw_j\le w$. Fix $i\in I$. Suppose $\mu(G^c)\le b$ and, on the support points in $G$,
--   $$\sum_{j\ne i}w_jA_{ij}(x)\le d,\qquad 0\le d\le w,\qquad pd\le\frac25.$$
--   For $R\ge1$, set $F=(I+H/R)^{-1}$. Every joint vector $f$ in every finite workspace satisfies
--   $$\|D_iFf\|^2\le4\|FD_if\|^2+\frac pR\|f\|^2+\frac{64p^2w^2b}{R^2}\|f\|_\infty^2.$$
--   The event $G$ may depend on every input coordinate. In particular it is not required to be determined outside a block or outside $i$. This retains the exact ordinary and rare-input coefficients.
--
--   Differences from the source:
--   - encoding: finite complex Hilbert spaces and square-root probability-weighted joint vectors → Euclidean workspaces and support functions with weighted inner products, norms and kernel adjoints; reason: choosing an orthonormal basis and sending f(x) to √ρ(x)f(x) is an isometric change of coordinates; every finite workspace is represented
--   - encoding: the interaction condition on the event G in the input space → the interaction condition on support points belonging to G; reason: the input Hilbert space is supported on Ω = supp μ; zero-probability inputs do not enter the conditional operators
-- source:
--   Arjan Cornelissen, Amin Shiraz Gilani, Xingyu Zhou, STOC 2027 submission #1375 (October 2026), Lemma 4.6, (4.28), p. 24

import Definitions.Def_QuantumTriangleFinding_Search_ConditionalOperators

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace QuantumTriangleFinding.Search

/-- Lemma 4.6, p.24: G may depend on every coordinate; no outside-coordinate condition. -/
theorem moving_difference_average {I W : Type} [Fintype I] [DecidableEq I] [Fintype W]
    (p : ℝ) (hp : 0 < p) (hp2 : p ≤ 1 / 2)
    (ℱ : Finset (Finset I)) (hℱ : ∀ C ∈ ℱ, C.Nonempty)
    (weights : I → ℝ) (hw : ∀ j, 0 ≤ weights j) (w : ℝ) (hsum : ∑ j, weights j ≤ w)
    (i : I) (G : Set (I → Bool)) (b d : ℝ)
    (hbad : eventProb (conditionedBernoulli p ℱ) Gᶜ ≤ b)
    (hd : 0 ≤ d) (hdw : d ≤ w) (hpd : p * d ≤ 2 / 5)
    (hcount : ∀ x : Support (conditionedBernoulli p ℱ), x.val ∈ G →
      (∑ j ∈ Finset.univ.erase i, weights j * interaction ℱ i j x.val) ≤ d)
    (R : ℝ) (hR : 1 ≤ R) (f : Joint (conditionedBernoulli p ℱ) W) :
    let μ := conditionedBernoulli p ℱ
    let Di := conditionalDifference μ i
    let F := resolvent (weightedDifferences μ weights) R
    normSq μ (applyKernel Di (applyKernel F f)) ≤
      4 * normSq μ (applyKernel F (applyKernel Di f)) + p / R * normSq μ f +
        64 * p ^ 2 * w ^ 2 * b / R ^ 2 * infinityNorm μ f ^ 2 := by sorry

end QuantumTriangleFinding.Search
