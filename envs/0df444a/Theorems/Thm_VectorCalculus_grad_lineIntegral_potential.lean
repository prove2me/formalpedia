-- Prove2me | Theorems.Thm_VectorCalculus_grad_lineIntegral_potential
-- name    : VectorCalculus.grad_lineIntegral_potential
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T00:17:56.988404+00:00
-- url     : https://prove2.me/theorems/64bb9c7b-f7a0-4686-8a3f-d6ad3e75bfa7
-- title:
--   Construction of the potential: $\nabla\phi = \mathbf{F}$ for $\phi(y)=\int_{C(y)}\mathbf{F}\cdot d\mathbf{x}$
-- statement:
--   Let $\mathbf F$ be a continuous vector field on $\mathbb R^n$ whose line integral around every closed $C^1$ curve vanishes. Define a scalar field by integrating $\mathbf F$ from the origin to the point $y$ along the straight segment $t\mapsto ty$, $t\in[0,1]$:
--
--   $$\phi(y) = \int_{C(y)} \mathbf F\cdot d\mathbf x = \int_0^1 \mathbf F(ty)\cdot y\, dt .$$
--
--   Then $\nabla\phi = \mathbf F$ at every point. This is the converse construction of §1.3.2, where the potential is built by integrating the field along a curve from the origin — the hypothesis of vanishing circulation being what makes the choice of curve immaterial.
-- source:
--   David Tong, Vector Calculus, University of Cambridge Part IA Mathematical Tripos lecture notes, http://www.damtp.cam.ac.uk/user/tong/vc.html, §1.3.2 (pp. 21–22), the converse half of the Claim: $\phi(\mathbf y) = \int_{C(\mathbf y)}\mathbf F\cdot d\mathbf x$ satisfies $\nabla\phi = \mathbf F$

import Definitions.Def_VectorCalculus_lineIntegral
import Definitions.Def_VectorCalculus_grad

namespace VectorCalculus

theorem grad_lineIntegral_potential {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : Continuous F)
    (hclosed : ∀ (x : ℝ → (Fin n → ℝ)) (a b : ℝ), a ≤ b → ContDiff ℝ 1 x → x a = x b →
      lineIntegral F x a b = 0) (y : Fin n → ℝ) :
    grad (fun z => lineIntegral F (fun t => t • z) 0 1) y = F y := by sorry

end VectorCalculus
