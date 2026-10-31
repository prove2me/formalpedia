-- Prove2me | Theorems.Thm_TensorAHPE_proposition_3_2
-- name    : TensorAHPE.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:35.155989+00:00
-- url     : https://prove2.me/theorems/865717d0-98b2-4322-b343-e0397e92b314
-- title:
--   Proposition 3.2: (3.11) and $\|\lambda v+y-\tilde x\|^2+2\lambda\epsilon\le(\sigma_u+\hat\sigma)^2\|y-\tilde x\|^2$
-- statement:
--   Assume the setting of problem (1.1) ($f$ convex, $d\ge1$ times differentiable with $L_d$-Lipschitz $\nabla^d f$; $h$ proper closed convex) and parameters $M,\hat\sigma,\sigma_l,\sigma_u$ as in STEP 1 of Algorithm 2. Let $(y,u,\epsilon)$ be a $\hat\sigma$-approximate solution of (2.5) at $(\lambda,\tilde x)$ such that
--
--   $$\frac{d!\,\sigma_l}{L_d+M}\le\lambda\|y-\tilde x\|^{d-1}\le\frac{d!\,\sigma_u}{L_d+M}\qquad(3.7)$$
--
--   and define $v:=\nabla f(y)+u-\nabla f_{\tilde x}(y)$. Then
--
--   $$\|\lambda v+y-\tilde x\|^2+2\lambda\epsilon\le\Big(\hat\sigma+\lambda\frac{L_d+M}{d!}\|y-\tilde x\|^{d-1}\Big)^2\|y-\tilde x\|^2\qquad(3.11)$$
--
--   and consequently
--
--   $$\|\lambda v+y-\tilde x\|^2+2\lambda\epsilon\le\sigma^2\|y-\tilde x\|^2\quad\text{with }\sigma=\sigma_u+\hat\sigma.\qquad(3.12)$$
--
--   This shows that each step of Algorithm 2 satisfying (3.7) meets the relative-error condition (3.2) of the A-HPE framework.
--
--   Differences from the source:
--   - encoding: (3.7) with λ_{k+1}, y_{k+1}, x̃_k; σ_u, σ̂, M parameters of Algorithm 2 → (3.7) for λ, y, x̃; parameters satisfying STEP 1 (Params.Admissible); reason: the proposition reads (3.7) for the given triple and names σ_u as an input parameter of Algorithm 2
--   - encoding: ℝⁿ with the Euclidean norm; f d times differentiable with ‖∇ᵈf(x) − ∇ᵈf(y)‖ ≤ L_d‖x − y‖ in the tensor operator norm → EuclideanSpace ℝ (Fin n); ContDiff ℝ d f and the Lipschitz bound on iteratedFDeriv ℝ d f in the multilinear operator norm, with 0 ≤ L; reason: the operator norm of a symmetric tensor over unit vectors equals Mathlib's multilinear norm (flip the sign of one argument); a d-th derivative that is Lipschitz is continuous; a Lipschitz constant is nonnegative
--   - encoding: h : ℝⁿ → (−∞, +∞] proper closed convex, F = f + h → h : E → EReal never ⊥, somewhere finite, lower semicontinuous, with convex epigraph; F x = (f x : EReal) + h x; reason: Lean convention for extended-valued convex functions; same instances
-- source:
--   Jiang, Wang & Zhang, An Optimal High-Order Tensor Method for Convex Optimization, arXiv:1812.06557v3, Proposition 3.2, p.9

import Mathlib
import Definitions.Def_TensorAHPE_Algorithm2

namespace TensorAHPE

/-- **Proposition 3.2.**
Jiang, Wang & Zhang, arXiv:1812.06557v3, Proposition 3.2, p.9: "Let (y, u, ε) be a σ̂-approximate
solution of (2.5) at (λ, x̃) such that (3.7) holds. Define v := ∇f(y) + u − ∇f_x̃(y). Then,
‖λv + y − x̃‖² + 2λε ≤ (σ̂ + λ((L_d + M)/d!)‖y − x̃‖^{d−1})² ‖y − x̃‖². (3.11)
Consequently, ‖λv + y − x̃‖² + 2λε ≤ σ²‖y − x̃‖² with σ = σ_u + σ̂, (3.12)
where σ_u is a input paramter in Algorithm 2 and also appears in (3.7)."

Setting: problem (1.1) under (2.2) (`P : Problem n d`), `d ≥ 1`, parameters satisfying STEP 1 of
Algorithm 2 (p.8); (3.7) is read with `λ, y, x̃` in place of `λ_{k+1}, y_{k+1}, x̃_k`.

**Formalization Note.** `∇f_x̃` is the `gradient` of `model P.f d M x̃` (Eq. (2.4)). -/
theorem proposition_3_2 {n d : ℕ} (P : Problem n d) (hd : 1 ≤ d) (prm : Params)
    (hprm : prm.Admissible d P.L) (lam : ℝ) (xt y u : EuclideanSpace ℝ (Fin n)) (ε : ℝ)
    (hsol : IsApproxSol P.f P.h d prm.M prm.σhat lam xt y u ε)
    (h37 : Cond37 d P.L prm lam y xt) :
    ‖lam • (gradient P.f y + u - gradient (model P.f d prm.M xt) y) + y - xt‖ ^ 2 + 2 * lam * ε
        ≤ (prm.σhat + lam * ((P.L + prm.M) / (d.factorial : ℝ)) * ‖y - xt‖ ^ (d - 1)) ^ 2
          * ‖y - xt‖ ^ 2 ∧
      ‖lam • (gradient P.f y + u - gradient (model P.f d prm.M xt) y) + y - xt‖ ^ 2 + 2 * lam * ε
        ≤ (prm.σu + prm.σhat) ^ 2 * ‖y - xt‖ ^ 2 := by sorry

end TensorAHPE
