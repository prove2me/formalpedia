-- Prove2me | Theorems.Thm_VectorCalculus_lineIntegral_grad
-- name    : VectorCalculus.lineIntegral_grad
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T00:13:54.959795+00:00
-- url     : https://prove2.me/theorems/247b7f87-173f-4d29-965a-1477d7fcfb75
-- title:
--   $\int_C \nabla\phi\cdot d\mathbf{x} = \phi(\mathbf{b}) - \phi(\mathbf{a})$
-- statement:
--   Let $\phi$ be a continuously differentiable scalar field on $\mathbb R^n$ and let $x$ be a continuously differentiable curve. Then the line integral of the gradient field $\nabla\phi$ along $x$ between parameter values $a$ and $b$ depends only on the endpoints:
--
--   $$\int_C \nabla\phi\cdot d\mathbf x = \phi\bigl(x(b)\bigr) - \phi\bigl(x(a)\bigr).$$
--
--   This is the chain rule followed by the fundamental theorem of calculus, and it is the forward half of the chapter's main claim.
-- source:
--   David Tong, Vector Calculus, University of Cambridge Part IA Mathematical Tripos lecture notes, http://www.damtp.cam.ac.uk/user/tong/vc.html, §1.3.2 (p. 21), the computation $\int_C \mathbf F\cdot d\mathbf x = [\phi(x(t))]_{t_a}^{t_b} = \phi(\mathbf b) - \phi(\mathbf a)$ for $\mathbf F = \nabla\phi$

import Definitions.Def_VectorCalculus_lineIntegral
import Definitions.Def_VectorCalculus_grad

namespace VectorCalculus

theorem lineIntegral_grad {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ)
    (x : ℝ → (Fin n → ℝ)) (hx : ContDiff ℝ 1 x) (a b : ℝ) :
    lineIntegral (grad φ) x a b = φ (x b) - φ (x a) := by sorry

end VectorCalculus
