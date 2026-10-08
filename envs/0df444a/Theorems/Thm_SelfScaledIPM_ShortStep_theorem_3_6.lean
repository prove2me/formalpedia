-- Prove2me | Theorems.Thm_SelfScaledIPM_ShortStep_theorem_3_6
-- name    : SelfScaledIPM.ShortStep.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:28.697129+00:00
-- url     : https://prove2.me/theorems/7240cd57-d38f-4fdb-9931-344e2aead1b6
-- title:
--   Theorem 3.6, p. 9 — local norms and |·| at x and x̃ with |x̃ − x|_x ≤ δ < 1 differ by factors (1 ± p_±)^{±1}, (1 ± δ)^{±1}
-- statement:
--   Let $K$ be a self-scaled cone with a $\nu$-self-scaled barrier $F$. Let $x, \tilde x \in \operatorname{int} K$ with $|\tilde x - x|_x \le \delta < 1$, and put $p = x - \tilde x$, $p_+ = \sigma_x(p)$, $p_- = \sigma_x(-p)$, so that $p_+ \le \delta$ and $p_- \le \delta$. Then for every primal vector $v \in E$ and dual vector $u \in E^*$:
--   $$(1+\delta)^{-1}\|v\|_x \le (1+p_-)^{-1}\|v\|_x \le \|v\|_{\tilde x} \le (1-p_+)^{-1}\|v\|_x \le (1-\delta)^{-1}\|v\|_x,\qquad (3.9)$$
--   $$(1-\delta)\|u\|_x \le (1-p_+)\|u\|_x \le \|u\|_{\tilde x} \le (1+p_-)\|u\|_x \le (1+\delta)\|u\|_x,\qquad (3.10)$$
--   $$(1+\delta)^{-1}|v|_x \le (1+p_-)^{-1}|v|_x \le |v|_{\tilde x} \le (1-p_+)^{-1}|v|_x \le (1-\delta)^{-1}|v|_x,\qquad (3.11)$$
--   $$(1-\delta)|u|_x \le (1-p_+)|u|_x \le |u|_{\tilde x} \le (1+p_-)|u|_x \le (1+\delta)|u|_x.\qquad (3.12)$$
--
--   The theorem compares the local geometry at two nearby interior points; it is what converts bounds at the current iterate into bounds at the next one.
--
--   **Formalization Note** The paper prints the middle factors of (3.12) as $(1-p_-)$ and $(1+p_+)$. That form contradicts the paper's own proof, which obtains (3.12) from (3.11) with the roles of the two points exchanged through Lemma 3.3, and it is false for $K = \mathbb R_+$, $F = -\ln$, where $|u|_{\tilde x} = (\tilde x/x)|u|_x$. The statement here uses the corrected factors $(1-p_+)$ and $(1+p_-)$, the same as in (3.10); the outer bounds are as printed. Norms: $\|v\|_x$ is `lnorm F x v`, $\|u\|_x$ is `dnorm F x u`, $|v|_x$ is `absn K x v`, and $|u|_x$ is `absn K* (-F'(x)) u`.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 9, Theorem 3.6, (3.9)–(3.12); middle factors of (3.12) corrected

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace

namespace SelfScaledIPM.ShortStep

/-- **Theorem 3.6** (p. 9). Let `x, x̃ ∈ int K` with `|x̃ − x|_x ≤ δ < 1`, and put `p = x − x̃`,
`p₊ = σ_x(p)`, `p₋ = σ_x(−p)`. Then `p₊ ≤ δ`, `p₋ ≤ δ`, and for every `v ∈ E`, `u ∈ E*` the
chains (3.9)–(3.12) hold. Lean names: `lnorm F x v = ‖v‖_x` (v ∈ E), `dnorm F x u = ‖u‖_x`
(u ∈ E*), `absn K x v = |v|_x` (v ∈ E), `absn K* (−F'(x)) u = |u|_x` (u ∈ E*).
The middle factors of (3.12) are stated as `(1 − p₊)` and `(1 + p₋)`: the printed
`(1 − p₋)`, `(1 + p₊)` contradicts the paper's own proof and fails for `K = ℝ₊`, `F = −ln`. -/
theorem theorem_3_6 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (x xt : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (hxt : xt ∈ interior K)
    (δ : ℝ) (hδ1 : δ < 1) (hδ : absn K x (xt - x) ≤ δ) :
    let p := x - xt
    let pp := sigma K x p
    let pm := sigma K x (-p)
    pp ≤ δ ∧ pm ≤ δ ∧
    ∀ v u : EuclideanSpace ℝ (Fin n),
      -- (3.9)
      ((1 + δ)⁻¹ * lnorm F x v ≤ (1 + pm)⁻¹ * lnorm F x v ∧
        (1 + pm)⁻¹ * lnorm F x v ≤ lnorm F xt v ∧
        lnorm F xt v ≤ (1 - pp)⁻¹ * lnorm F x v ∧
        (1 - pp)⁻¹ * lnorm F x v ≤ (1 - δ)⁻¹ * lnorm F x v) ∧
      -- (3.10)
      ((1 - δ) * dnorm F x u ≤ (1 - pp) * dnorm F x u ∧
        (1 - pp) * dnorm F x u ≤ dnorm F xt u ∧
        dnorm F xt u ≤ (1 + pm) * dnorm F x u ∧
        (1 + pm) * dnorm F x u ≤ (1 + δ) * dnorm F x u) ∧
      -- (3.11)
      ((1 + δ)⁻¹ * absn K x v ≤ (1 + pm)⁻¹ * absn K x v ∧
        (1 + pm)⁻¹ * absn K x v ≤ absn K xt v ∧
        absn K xt v ≤ (1 - pp)⁻¹ * absn K x v ∧
        (1 - pp)⁻¹ * absn K x v ≤ (1 - δ)⁻¹ * absn K x v) ∧
      -- (3.12), middle factors corrected
      ((1 - δ) * absn (ConvexOptimization.dualCone K) (-gradient F x) u ≤
          (1 - pp) * absn (ConvexOptimization.dualCone K) (-gradient F x) u ∧
        (1 - pp) * absn (ConvexOptimization.dualCone K) (-gradient F x) u ≤
          absn (ConvexOptimization.dualCone K) (-gradient F xt) u ∧
        absn (ConvexOptimization.dualCone K) (-gradient F xt) u ≤
          (1 + pm) * absn (ConvexOptimization.dualCone K) (-gradient F x) u ∧
        (1 + pm) * absn (ConvexOptimization.dualCone K) (-gradient F x) u ≤
          (1 + δ) * absn (ConvexOptimization.dualCone K) (-gradient F x) u) := by sorry

end SelfScaledIPM.ShortStep
