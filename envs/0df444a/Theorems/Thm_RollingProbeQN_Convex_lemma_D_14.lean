-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_lemma_D_14
-- name    : RollingProbeQN.Convex.lemma_D_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:19:45.077289+00:00
-- url     : https://prove2.me/theorems/65c03bf6-3ea3-424b-ac1c-54d6012cd2d8
-- title:
--   Lemma D.14 — the two residual certificates of a regularized model step
-- statement:
--   Let $F$ be convex with an $L_2$-Lipschitz Hessian, $B\succeq0$, $\lambda>0$, $y\in\mathbb R^d$ and $r=-(B+\lambda^{-1}I)^{-1}\nabla F(y)$. Then
--
--   $$\|r+\lambda\nabla F(y+r)\|\ \le\ \lambda\Big(\|B-\nabla^2F(y)\|_{\mathrm{op}}+\frac{L_2}{2}\|r\|\Big)\|r\| .$$
--
--   If moreover $0\preceq\nabla^2F(v)\preceq LI$ for all $v$ on the segment $[y,y+r]$ and $B\preceq LI$, then
--
--   $$\|r+\lambda\nabla F(y+r)\|\ \le\ \lambda L\|r\| .$$
--
--   With $\lambda(\|B-\nabla^2F(y)\|_{\mathrm{op}}+L_2\|r\|/2)\le\sigma$, or $\lambda L\le\sigma$, the step satisfies the relative proximal condition (2).
--
--   Differences from the source:
--   - encoding: a function with an L₂-Lipschitz Hessian → ContDiff ℝ 2 F and ‖hess F x − hess F y‖ ≤ L₂‖x − y‖; reason: a Lipschitz Hessian exists and is continuous, so F is C²; same functions
--   - reading: "0 ⪯ ∇²F(v), B ⪯ LI everywhere on [y, y + r]" → 0 ⪯ ∇²F(v) ⪯ LI for v ∈ segment y (y + r), and B ⪯ LI; reason: both matrices lie between 0 and LI; B ⪰ 0 is already assumed; this is how the proof on p. 43 uses it
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Lemma D.14, p. 42

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_hess
import Definitions.Def_RollingProbeQN_Convex_modelStep

namespace RollingProbeQN.Convex

/-- **Lemma D.14 (Two elementary certificates).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Lemma D.14, p. 42: "For a convex differentiable function `F` with `L2`-Lipschitz Hessian,
`B ⪰ 0`, `λ > 0`, and `r = −(B + λ^{−1}I)^{−1}∇F(y)`,
`‖r + λ∇F(y + r)‖ ≤ λ(‖B − ∇²F(y)‖op + (L2/2)‖r‖)‖r‖`. If in addition `0 ⪯ ∇²F(v), B ⪯ LI`
everywhere on `[y, y + r]`, then `‖r + λ∇F(y + r)‖ ≤ λL‖r‖`."

**Formalization Note.** "Convex differentiable with `L₂`-Lipschitz Hessian" is `ConvexOn`,
`ContDiff ℝ 2` and the Lipschitz bound. The second hypothesis is read as
`0 ⪯ ∇²F(v) ⪯ LI` for `v ∈ [y, y + r]` and `B ⪯ LI` (with `B ⪰ 0` already assumed). -/
theorem lemma_D_14 {d : ℕ} {F : EuclideanSpace ℝ (Fin d) → ℝ} {L₂ : ℝ}
    (hconv : ConvexOn ℝ Set.univ F) (hF : ContDiff ℝ 2 F)
    (hL : ∀ x y : EuclideanSpace ℝ (Fin d), ‖hess F x - hess F y‖ ≤ L₂ * ‖x - y‖)
    (B : Matrix (Fin d) (Fin d) ℝ) (hB : B.PosSemidef) (lam : ℝ) (hlam : 0 < lam)
    (y : EuclideanSpace ℝ (Fin d)) :
    ‖modelStep B lam (gradient F y) + lam • gradient F (y + modelStep B lam (gradient F y))‖ ≤
        lam * (‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) B - hess F y‖ + L₂ / 2 * ‖modelStep B lam (gradient F y)‖)
          * ‖modelStep B lam (gradient F y)‖ ∧
    ∀ L : ℝ,
      (∀ v ∈ segment ℝ y (y + modelStep B lam (gradient F y)), ∀ u : EuclideanSpace ℝ (Fin d),
        0 ≤ inner ℝ (hess F v u) u ∧ inner ℝ (hess F v u) u ≤ L * ‖u‖ ^ 2) →
      (L • (1 : Matrix (Fin d) (Fin d) ℝ) - B).PosSemidef →
      ‖modelStep B lam (gradient F y) + lam • gradient F (y + modelStep B lam (gradient F y))‖ ≤
        lam * L * ‖modelStep B lam (gradient F y)‖ := by sorry

end RollingProbeQN.Convex
