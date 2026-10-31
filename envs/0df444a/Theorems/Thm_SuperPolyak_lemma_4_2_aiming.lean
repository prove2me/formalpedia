-- Prove2me | Theorems.Thm_SuperPolyak_lemma_4_2_aiming
-- name    : SuperPolyak.lemma_4_2_aiming
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:51.650989+00:00
-- url     : https://prove2.me/theorems/3b7d2a47-69ff-4a75-bf89-430784dc1b63
-- title:
--   Lemma 4.2 (Aiming): $\langle v,x-\hat x\rangle\ge\frac\mu2\operatorname{dist}(x,X^*)$ (corrected: open ball $\|x-\bar x\|<\delta$)
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be locally Lipschitz, $\bar x\in X^*$, $\delta>0$, and suppose that (A1) (sharpness, constant $\mu$) and (A2) ($(b)$-regularity, map $g$, constants $C_{(b)},\eta$) hold at $\bar x$. Fix a point $x$ with
--   $$
--   \|x-\bar x\|<\delta\qquad\text{and}\qquad \operatorname{dist}(x,X^*)\le\Big(\frac{\mu}{2C_{(b)}}\Big)^{1/\eta}.
--   $$
--   Then
--   1. $\langle v,x-\hat x\rangle\ge\dfrac{\mu}{2}\operatorname{dist}(x,X^*)$ for all $v\in g(x)$ and all $\hat x\in P_{X^*}(x)$ (display (16));
--   2. if $x\notin X^*$, then $\|v\|\ge\mu/2$ for all $v\in g(x)$.
--
--   Negative generalized gradients "aim" at the solution set. This is the basic estimate behind both PolyakSGM and PolyakBundle.
--
--   **Formalization Note** $f^*=f(\bar x)$; balls are open.
--
--   Differences from the source:
--
--   - correction: ‖x − x̄‖ ≤ δ → ‖x − x̄‖ < δ; reason: (A1) and (A2) hold only on the open ball B_δ(x̄); counterexample: d = 1, f = |·|, x̄ = 0, δ = µ = η = 1, C_(b) = 1/100, g(x) = {sign x} for 0 < |x| < 1, g(0) = {0}, g(x) = {0} for |x| ≥ 1 satisfies every assumption, but at x = 1 with v = 0 ∈ g(1), ⟨v, x − x̂⟩ = 0 < µ/2 = (µ/2)·dist(1, X*); every use in the paper is at a point of the open ball
--   - encoding: optimal value f* → f x̄, with x̄ ∈ X* a hypothesis; reason: x̄ ∈ X* gives f(x̄) = f*; same instances
-- source:
--   Charisopoulos & Davis, A superlinearly convergent subgradient method for sharp semismooth problems, arXiv:2201.04611v1, Lemma 4.2 (Aiming), display (16), p.22

import Mathlib
import Definitions.Def_SuperPolyak_Setting

namespace SuperPolyak

/-- **Lemma 4.2 (Aiming)**, corrected to the open ball (Charisopoulos & Davis,
arXiv:2201.04611v1, Lemma 4.2, display (16), p.22). Under the standing assumptions of §2 (p.7)
and Assumptions (A1), (A2) at `x̄` (in force throughout §4, p.22), fix `x` with `‖x − x̄‖ < δ` and
`dist(x, X*) ≤ (µ/(2C_(b)))^{1/η}`. Then
`⟨v, x − x̂⟩ ≥ (µ/2) dist(x, X*)` for all `v ∈ g(x)` and `x̂ ∈ P_{X*}(x)`, and, if `x ∉ X*`,
`‖v‖ ≥ µ/2` for all `v ∈ g(x)`.

**Formalization Note** The paper prints `‖x − x̄‖ ≤ δ`; (A1) and (A2) hold only on the open ball
`B_δ(x̄)`, and the closed-ball version is false (for `f = |·|` on `ℝ`, `x̄ = 0`, `δ = 1`, a map
`g` with `g(1) = {0}` satisfies every assumption, yet `⟨0, 1 − 0⟩ = 0 < µ/2` at `x = 1`). Every
use in the paper is at a point of the open ball. `f* = f x̄`. -/
theorem lemma_4_2_aiming {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d))}
    {xbar : EuclideanSpace ℝ (Fin d)} {δ μ Cb η : ℝ}
    (hf : LocallyLipschitz f) (hxbar : xbar ∈ solutionSet f) (hδ : 0 < δ)
    (hA1 : Sharp f xbar δ μ) (hA2 : BRegular f g xbar δ Cb η)
    {x : EuclideanSpace ℝ (Fin d)} (hx : ‖x - xbar‖ < δ)
    (hdist : Metric.infDist x (solutionSet f) ≤ (μ / (2 * Cb)) ^ (1 / η)) :
    (∀ v ∈ g x, ∀ xhat ∈ nearestPoints (solutionSet f) x,
        μ / 2 * Metric.infDist x (solutionSet f) ≤ inner ℝ v (x - xhat)) ∧
      (x ∉ solutionSet f → ∀ v ∈ g x, μ / 2 ≤ ‖v‖) := by sorry

end SuperPolyak
