-- Prove2me | Theorems.Thm_TegmarkDimensionality_no_gravity_below_three_space_dims
-- name    : TegmarkDimensionality.no_gravity_below_three_space_dims
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T03:30:24.363502+00:00
-- url     : https://prove2.me/theorems/1a10b307-5959-4b93-a4b1-8461c8616484
-- title:
--   No gravitational force in general relativity for $n<3$
-- statement:
--   Let $n<3$, so spacetime has dimension $n+1\le3$. Let $g$ be a nondegenerate symmetric $(n+1)\times(n+1)$ real matrix (a metric at a point) and let $R_{abcd}$ be a real 4-index array with the algebraic symmetries of the Riemann tensor:
--   $$R_{abcd}=-R_{bacd}=-R_{abdc},\qquad R_{abcd}=R_{cdab},\qquad R_{abcd}+R_{acdb}+R_{adbc}=0.$$
--   If its Ricci contraction vanishes, $\sum_{a,c}(g^{-1})^{ac}R_{abcd}=0$ for all $b,d$, then $R_{abcd}=0$ for all indices.
--
--   Vacuum solutions of Einstein's equations are Ricci-flat. So when $n<3$ they are flat at every point, there are no tidal forces, and matter exerts no gravitational force on distant test particles.
--
--   **Formalization Note** The statement is pointwise and purely algebraic. It formalizes the curvature-algebra fact behind the paper's remark.
-- source:
--   M. Tegmark, *On the dimensionality of spacetime*, Class. Quantum Grav. 14 (1997) L69–L75, https://doi.org/10.1088/0264-9381/14/4/002, p. L71, second paragraph ('there is no gravitational force in general relativity with n < 3'), citing Misner–Thorne–Wheeler p. 1205 and Deser–Jackiw–'t Hooft 1984

import Mathlib

namespace TegmarkDimensionality

/-- In a spacetime of dimension `n + 1` with `n < 3` space dimensions, every tensor
`R_{abcd}` with the algebraic symmetries of the Riemann tensor whose Ricci contraction
with respect to a nondegenerate symmetric metric `g` vanishes is identically zero
(vacuum general relativity has no curvature, hence no gravitational force). -/
theorem no_gravity_below_three_space_dims (n : ℕ) (hn : n < 3)
    (g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hg : g.IsSymm) (hdet : g.det ≠ 0)
    (R : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ)
    (hR₁ : ∀ a b c d, R a b c d = -R b a c d)
    (hR₂ : ∀ a b c d, R a b c d = -R a b d c)
    (hR₃ : ∀ a b c d, R a b c d = R c d a b)
    (hBianchi : ∀ a b c d, R a b c d + R a c d b + R a d b c = 0)
    (hRicci : ∀ b d, ∑ a, ∑ c, g⁻¹ a c * R a b c d = 0) :
    ∀ a b c d, R a b c d = 0 := by sorry

end TegmarkDimensionality
