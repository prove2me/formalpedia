-- Prove2me | Theorems.Thm_ProjSelfConcordant_ConicExt_Supplement_theorem_4_3
-- name    : ProjSelfConcordant.ConicExt.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:20:33.535302+00:00
-- url     : https://prove2.me/theorems/66f9e235-c940-4c13-92a3-e992d6a1dd5c
-- title:
--   Theorem 4.3, p. 11 — negative curvature iff ½(σₓ(h) − f′(x)[h])C(x)[·,·,h] ⪯ (σₓ(h) − f′(x)[h])²G(x) − G(x)[·,h]G(x)[·,h]ᵀ
-- statement:
--   Let $X\subset\mathbb R^n$ be a regular convex set with interior $X^o$, let $\nu\ge2$, and let $f$ be a projectively self-concordant barrier on $X$ with parameter $\gamma=(\nu-2)/\sqrt{\nu-1}$. Let $G$ and $C$ be the affine metric and the cubic form of $f$ (Definition 1.4) and $\sigma_x(h)=\inf\{t^{-1}\mid t>0,\ x+th\in X\}$.
--
--   Say that $f$ has *negative curvature* (Definition 4.2) if $F(t,x)=\nu(-\log t+f(t^{-1}x))$ satisfies $F'''(z)[v,v,u]\le0$ for all directions $v$, all $z$ in the interior of the conic extension $K=\overline{\{(t,x)\mid t>0,\ t^{-1}x\in X^o\}}$ and all $u\in K$.
--
--   Then $f$ has negative curvature if and only if for all $x\in X^o$ and all $h\in\mathbb R^n$
--   $$\tfrac12\bigl(\sigma_x(h)-f'(x)[h]\bigr)\,C(x)[\cdot,\cdot,h]\ \preceq\ \bigl(\sigma_x(h)-f'(x)[h]\bigr)^2G(x)-G(x)[\cdot,h]\,G(x)[\cdot,h]^T,$$
--   that is, for every direction $v$,
--   $$\tfrac12\bigl(\sigma_x(h)-f'(x)[h]\bigr)C(x)[v,v,h]\le\bigl(\sigma_x(h)-f'(x)[h]\bigr)^2G(x)[v,v]-\bigl(G(x)[v,h]\bigr)^2.$$
--
--   The theorem rewrites the cone condition of negative curvature, defined on the conic extension, as a condition on the derivatives of $f$ along with the distance to the boundary.
--
--   **Formalization Note** The order $\preceq$ between symmetric bilinear forms is tested on every direction $v$. $f'(x)[h]$ is `fderiv ℝ f x h`; $\sigma_x(h)$ is a real `sInf`, the genuine infimum for $x\in X^o$, and is $0$ in unbounded directions. The hypothesis $\nu\ge2$ is the range for which $\gamma\ge0$ is defined.
--
--   Differences from the source:
--   - encoding: γ = (ν − 2)/√(ν − 1) with γ ≥ 0 required by Definition 1.4 → explicit hypothesis 2 ≤ ν; reason: exactly the ν for which the formula defines a real γ ≥ 0; Lean's √ of a negative number is 0
--   - reading: "the conic extension K of X" for a closed X → the closure of the open cone {(t, x) | t > 0, t⁻¹x ∈ Xᵒ}; reason: the negative-curvature condition of §4 is stated for a regular (closed) cone, and the closure of this open cone is the closed cone over X; its interior is the open cone on which F is defined
--   - encoding: functions and derivatives on open subsets of ℝⁿ → total functions on EuclideanSpace ℝ (Fin n), with Fréchet derivatives evaluated on the stated open domains; reason: every source function extends outside its domain; derivatives at interior points depend only on local values, and the Euclidean inner product identifies covectors with gradients when needed
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, p. 11, Theorem 4.3 (with Definition 4.2, p. 11, and the negative-curvature condition, p. 10)

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting
import Definitions.Def_ProjSelfConcordant_ConicExt_Supplement_Barrier

namespace ProjSelfConcordant.ConicExt.Supplement

/-- Theorem 4.3, p. 11: a projectively self-concordant barrier `f` on a regular convex set
`X ⊂ ℝⁿ`, with parameter `γ = (ν − 2)/√(ν − 1)`, has negative curvature (Definition 4.2) if and
only if for all `x ∈ Xᵒ` and `h ∈ ℝⁿ`
`½(σₓ(h) − f′(x)[h]) C(x)[·,·,h] ⪯ (σₓ(h) − f′(x)[h])² G(x) − G(x)[·,h] G(x)[·,h]ᵀ`,
the Loewner order being tested on every direction `v`. -/
theorem theorem_4_3 {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : RegularConvexSet X) (f : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 2 ≤ ν)
    (hf : ProjBarrier ((ν - 2) / Real.sqrt (ν - 1)) X f) :
    ProjNegCurv ν X f ↔
      ∀ x ∈ interior X, ∀ h v : EuclideanSpace ℝ (Fin n),
        (1 / 2 : ℝ) * (sigmaGauge X x h - fderiv ℝ f x h) * cubicForm f x v v h
          ≤ (sigmaGauge X x h - fderiv ℝ f x h) ^ 2 * affMetric f x v v
            - affMetric f x v h * affMetric f x v h := by sorry

end ProjSelfConcordant.ConicExt.Supplement
