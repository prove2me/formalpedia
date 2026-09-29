-- Prove2me | Theorems.Thm_VectorCalculus_conservative_partialDeriv_symm
-- name    : VectorCalculus.conservative_partialDeriv_symm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T00:19:23.642922+00:00
-- url     : https://prove2.me/theorems/18744336-c7f6-4f2a-90a9-8fa5024522e4
-- title:
--   Necessary condition (1.17): $\partial_i F_j = \partial_j F_i$
-- statement:
--   If a vector field $\mathbf F$ on $\mathbb R^n$ is the gradient of a twice continuously differentiable potential $\phi$, then its components satisfy the symmetry relation
--
--   $$\frac{\partial F_j}{\partial x^i} = \frac{\partial F_i}{\partial x^j}\qquad\text{for all } i, j,$$
--
--   because both sides are the mixed second partial derivative of $\phi$ and the order of partial differentiation is immaterial for sufficiently well-behaved functions. This is the standard test (1.17) used to rule out conservativity.
-- source:
--   David Tong, Vector Calculus, University of Cambridge Part IA Mathematical Tripos lecture notes, http://www.damtp.cam.ac.uk/user/tong/vc.html, §1.3.2 (p. 23), equation (1.17): $\partial F_i/\partial x^j = \partial^2\phi/\partial x^i \partial x^j = \partial F_j/\partial x^i$

import Definitions.Def_VectorCalculus_grad

namespace VectorCalculus

theorem conservative_partialDeriv_symm {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ) (hFφ : ∀ y, F y = grad φ y)
    (i j : Fin n) (y : Fin n → ℝ) :
    partialDeriv (fun z => F z j) i y = partialDeriv (fun z => F z i) j y := by sorry

end VectorCalculus
