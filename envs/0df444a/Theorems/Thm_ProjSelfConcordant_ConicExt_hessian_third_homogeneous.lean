-- Prove2me | Theorems.Thm_ProjSelfConcordant_ConicExt_hessian_third_homogeneous
-- name    : ProjSelfConcordant.ConicExt.hessian_third_homogeneous
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:58.176723+00:00
-- url     : https://prove2.me/theorems/f7d273ff-ae38-460b-b273-9d521debb975
-- title:
--   §2, p. 5 — F″(τx)[τh, τh] = F″(x)[h, h] and F‴(τx)[τh, τh, τh] = F‴(x)[h, h, h]
-- statement:
--   Let $D\subset\mathbb R^n$ be open and convex, $f$ a $C^3$ function on $D$, $\nu\in\mathbb R$, and $F(t,x)=\nu(-\log t+f(t^{-1}x))$ on the conic extension $K$. Then for all $x\in K$, all $h\in\mathbb R^{n+1}$ and all $\tau>0$,
--   $$F''(\tau x)[\tau h,\tau h]=F''(x)[h,h],\qquad F'''(\tau x)[\tau h,\tau h,\tau h]=F'''(x)[h,h,h].$$
--
--   This consequence of logarithmic homogeneity, $F(\tau x)=F(x)-\nu\log\tau$, reduces the verification of the affine conditions on $K$ to the slice $t=1$.
--
--   **Formalization Note** The identities hold for every real $\nu$ and are stated so; convexity of $D$ is the paper's standing assumption and is kept although it is not used.
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, p. 5, §2, proof of Theorem 1.5 ('By logarithmic homogeneity of F we have …')

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting

namespace ProjSelfConcordant.ConicExt

/-- §2, p. 5: logarithmic homogeneity of `F(t, x) = ν(−log t + f(t⁻¹x))` gives
`F″(τx)[τh, τh] = F″(x)[h, h]` and `F‴(τx)[τh, τh, τh] = F‴(x)[h, h, h]`
for all `x ∈ K`, all `h`, and all `τ > 0`. -/
theorem hessian_third_homogeneous {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (hDo : IsOpen D) (hDc : Convex ℝ D)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiffOn ℝ 3 f D) (ν : ℝ)
    (q : ℝ × EuclideanSpace ℝ (Fin n)) (hq : q ∈ conicExt D)
    (h : ℝ × EuclideanSpace ℝ (Fin n)) (τ : ℝ) (hτ : 0 < τ) :
    dk 2 (homExt ν f) (τ • q) (τ • h) = dk 2 (homExt ν f) q h ∧
      dk 3 (homExt ν f) (τ • q) (τ • h) = dk 3 (homExt ν f) q h := by sorry

end ProjSelfConcordant.ConicExt
