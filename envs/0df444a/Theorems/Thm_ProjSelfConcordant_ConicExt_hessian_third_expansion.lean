-- Prove2me | Theorems.Thm_ProjSelfConcordant_ConicExt_hessian_third_expansion
-- name    : ProjSelfConcordant.ConicExt.hessian_third_expansion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:55.576045+00:00
-- url     : https://prove2.me/theorems/cfe56746-4960-43dc-9d14-c1109e80fc48
-- title:
--   §2, p. 5 — F″ and F‴ at (1, x̃) along h = (0, ṽ) + α(1, x̃) in terms of f′, f″, f‴
-- statement:
--   Let $D\subset\mathbb R^n$ be open and convex, $f$ a $C^3$ function on $D$, $\nu\in\mathbb R$, and $F(t,x)=\nu(-\log t+f(t^{-1}x))$ on the conic extension $K$. Fix $\tilde x\in D$, a direction $\tilde v\in\mathbb R^n$ and $\alpha\in\mathbb R$, and put $x=(1,\tilde x)\in K$, $v=(0,\tilde v)$, $h=v+\alpha x=(\alpha,\tilde v+\alpha\tilde x)$. Then
--   $$F''(x)[h,h]=\nu\bigl(\alpha^2-2\alpha f'(\tilde x)[\tilde v]+f''(\tilde x)[\tilde v,\tilde v]\bigr),$$
--   $$F'''(x)[h,h,h]=\nu\bigl(-2\alpha^3+6\alpha^2 f'(\tilde x)[\tilde v]-6\alpha f''(\tilde x)[\tilde v,\tilde v]+f'''(\tilde x)[\tilde v,\tilde v,\tilde v]\bigr).$$
--
--   These expansions convert the affine conditions on $F$ at points of the slice $t=1$ into polynomial conditions in $\alpha$ whose coefficients are the derivatives of $f$; they are the computational core of both directions of Theorem 1.5.
--
--   **Formalization Note** The page states the identities for $\tilde v\ne0$ and $\nu\ge2$; they hold for every $\tilde v$ and every real $\nu$, and are stated so. Convexity of $D$ is the paper's standing assumption and is kept although it is not used.
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, p. 5, §2, proof of Theorem 1.5 (display after 'Consider h = v + αx')

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting

namespace ProjSelfConcordant.ConicExt

/-- §2, p. 5: at `x = (1, x̃)` and `h = v + αx = (0, ṽ) + α(1, x̃) = (α, ṽ + αx̃)`,
`F″(x)[h,h] = ν(α² − 2αf′(x̃)[ṽ] + f″(x̃)[ṽ,ṽ])` and
`F‴(x)[h,h,h] = ν(−2α³ + 6α²f′(x̃)[ṽ] − 6αf″(x̃)[ṽ,ṽ] + f‴(x̃)[ṽ,ṽ,ṽ])`. -/
theorem hessian_third_expansion {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (hDo : IsOpen D) (hDc : Convex ℝ D)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiffOn ℝ 3 f D) (ν : ℝ)
    (xt : EuclideanSpace ℝ (Fin n)) (hxt : xt ∈ D) (vt : EuclideanSpace ℝ (Fin n)) (α : ℝ) :
    dk 2 (homExt ν f) ((1 : ℝ), xt) (α, vt + α • xt)
        = ν * (α ^ 2 - 2 * α * dk 1 f xt vt + dk 2 f xt vt) ∧
      dk 3 (homExt ν f) ((1 : ℝ), xt) (α, vt + α • xt)
        = ν * (-2 * α ^ 3 + 6 * α ^ 2 * dk 1 f xt vt - 6 * α * dk 2 f xt vt + dk 3 f xt vt) := by sorry

end ProjSelfConcordant.ConicExt
