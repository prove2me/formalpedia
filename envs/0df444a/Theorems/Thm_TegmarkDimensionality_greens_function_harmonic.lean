-- Prove2me | Theorems.Thm_TegmarkDimensionality_greens_function_harmonic
-- name    : TegmarkDimensionality.greens_function_harmonic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T02:27:09.953579+00:00
-- url     : https://prove2.me/theorems/4c9b7af1-1e09-4203-bae4-d11e79f26445
-- title:
--   $r^{2-n}$ is harmonic away from the origin for $n>2$
-- statement:
--   Let $n>2$. The function $\phi(y)=|y|^{2-n}$ on $\mathbb R^n$ satisfies the Laplace equation at every point other than the origin:
--   $$\nabla^2\big(|y|^{2-n}\big)(x)=0\qquad\text{for all }x\in\mathbb R^n,\ x\neq0.$$
--
--   Up to a dimensional constant, $|y|^{2-n}$ is the potential of a point charge or point mass in $n$ space dimensions. The corresponding force decays like $r^{1-n}$, so the inverse-square law of $n=3$ becomes an inverse-cube law for $n=4$.
--
--   **Formalization Note** The statement records the harmonicity of $r^{2-n}$ away from the source. The distributional identity $\nabla^2 r^{2-n}=c_n\delta$ is not part of this milestone.
-- source:
--   M. Tegmark, *On the dimensionality of spacetime*, Class. Quantum Grav. 14 (1997) L69–L75, https://doi.org/10.1088/0264-9381/14/4/002, p. L70, first paragraph ('the fundamental Green's function of the Poisson equation ... is r^{2-n} for n > 2')

import Mathlib
import Definitions.Def_tegmark_laplacian

namespace TegmarkDimensionality

/-- For `n > 2`, the potential `r^{2-n}` of a point source in `ℝⁿ` satisfies the Laplace
equation away from the source. -/
theorem greens_function_harmonic (n : ℕ) (hn : 2 < n)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    laplacian (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ ((2 : ℝ) - n)) x = 0 := by sorry

end TegmarkDimensionality
