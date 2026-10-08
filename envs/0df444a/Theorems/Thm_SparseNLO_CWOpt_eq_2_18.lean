-- Prove2me | Theorems.Thm_SparseNLO_CWOpt_eq_2_18
-- name    : SparseNLO.CWOpt.eq_2_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:12:25.304882+00:00
-- url     : https://prove2.me/theorems/e11d2523-b98f-453b-89f6-e016d6c38c48
-- title:
--   (2.18), proof of Theorem 2.4 — f(x* − x*ₘeₘ − σx*ₘeᵢ) ≤ f(x*) − σx*ₘ∇ᵢf(x*) + L₂(f)(x*ₘ)² at a CW-minimum with ‖x*‖₀ = s
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable and bounded below with Lipschitz gradient (Assumption 2), let $0<s<n$, and let $L_2$ satisfy the local Lipschitz condition (2.15). Let $x^*$ be a coordinate-wise minimum of (P) with $\|x^*\|_0=s$. Let $i\in I_0(x^*)$, let $m$ be an index with $|x^*_m|=M_s(x^*)$, and set
--   $$\sigma=\operatorname{sgn}\big(x^*_m\nabla_i f(x^*)\big)\in\{-1,0,1\}.$$
--   Then
--   $$f\big(x^*-x^*_me_m-\sigma x^*_me_i\big)\le f(x^*)-\sigma x^*_m\nabla_i f(x^*)+L_2\,(x^*_m)^2 .$$
--
--   This is the estimate that, combined with the CW-minimality inequality $f(x^*)\le f(x^*-x^*_me_m-\sigma x^*_me_i)$ of (2.17), yields the bound $|\nabla_i f(x^*)|\le L_2M_s(x^*)$ on the zero coordinates in Theorem 2.4.
--
--   **Formalization Note** The statement is the first and the last member of the chain (2.18). The printed middle equality uses $\|x^*_me_m+\sigma x^*_me_i\|^2=2(x^*_m)^2$, which needs $\sigma^2=1$; when $\nabla_i f(x^*)=0$ ($\sigma=0$) the norm is $(x^*_m)^2$ and the inequality still holds because $L_2\ge0$. The sign is `SignType.sign` cast to $\mathbb R$, with $\operatorname{sgn}0=0$. The facts $m\in I_1(x^*)$ and $\nabla_m f(x^*)=0$ used on the page are consequences of the hypotheses, not assumptions.
-- source:
--   Beck, Eldar, Sparsity Constrained Nonlinear Optimization: Optimality Conditions and Algorithms, SIAM J. Optim. (2013), doi:10.1137/120869778 (source: arXiv:1203.4580v1), p. 12, §2.4, proof of Theorem 2.4, (2.18)

import Mathlib
import Definitions.Def_SparseNLO_CWOpt_Setting

namespace SparseNLO.CWOpt

/-- (2.18), proof of Theorem 2.4 (p. 12): let `x*` be a CW-minimum with `‖x*‖₀ = s`, let
`i ∈ I₀(x*)`, let `m` be an index with `|x*_m| = M_s(x*)`, and `σ = sgn(x*_m ∇_i f(x*))`. Then
`f(x* − x*_m e_m − σ x*_m e_i) ≤ f(x*) − σ x*_m ∇_i f(x*) + L2 (x*_m)²`. -/
theorem eq_2_18 {n s : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x) (hs : 0 < s) (hsn : s < n)
    (Lf : NNReal) (hLf : LipschitzWith Lf (gradient f))
    (L2 : ℝ) (hL2 : LocalLipschitz f L2)
    (xstar : EuclideanSpace ℝ (Fin n)) (hcw : IsCWMin f s xstar) (hxs : l0 xstar = s)
    (i : Fin n) (hi : i ∈ I0 xstar) (m : Fin n) (hm : |xstar m| = Ms s xstar) :
    f (xstar - EuclideanSpace.single m (xstar m)
        - EuclideanSpace.single i ((SignType.sign (xstar m * gradient f xstar i) : ℝ) * xstar m))
      ≤ f xstar - (SignType.sign (xstar m * gradient f xstar i) : ℝ) * xstar m * gradient f xstar i
        + L2 * xstar m ^ 2 := by sorry

end SparseNLO.CWOpt
