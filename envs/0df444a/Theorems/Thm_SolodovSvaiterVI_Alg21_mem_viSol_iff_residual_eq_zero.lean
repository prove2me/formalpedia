-- Prove2me | Theorems.Thm_SolodovSvaiterVI_Alg21_mem_viSol_iff_residual_eq_zero
-- name    : SolodovSvaiterVI.Alg21.mem_viSol_iff_residual_eq_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T10:22:48.571196+00:00
-- url     : https://prove2.me/theorems/f5c52460-dfb2-4026-95c5-f28740fa600d
-- title:
--   Solutions of $\mathrm{VI}(F, C)$ are exactly the zeros of the projected residual
-- statement:
--   Let $C$ be a nonempty closed convex subset of $\mathbb{R}^n$ and $F : \mathbb{R}^n \to \mathbb{R}^n$ any map. Let $S$ be the solution set of $\mathrm{VI}(F, C)$ and $r(x) = x - P_C[x - F(x)]$ the projected residual. Then for every $x \in \mathbb{R}^n$,
--
--   $$x \in S \iff r(x) = 0.$$
--
--   This is what makes $r(x^i) = 0$ a valid stopping test in Algorithm 2.1, and it is how the convergence proof certifies that a limit point is a solution.
--
--   **Formalization Note** The paper assumes $S$ nonempty throughout; here only $C \neq \emptyset$ is assumed (it follows from $S \ne \emptyset$ and is what makes $P_C$ well defined). No continuity of $F$ is needed.
-- source:
--   Solodov & Svaiter, A New Projection Method for Variational Inequality Problems, SIAM J. Control Optim. 37 (1999), p. 767, Section 2 (first paragraph)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_SolodovSvaiterVI_Alg21_residual

namespace SolodovSvaiterVI.Alg21

/-- Solodov–Svaiter, Section 2, p. 767: solutions of `VI(F, C)` coincide with the zeros of the
projected residual `r(x) = x − P_C[x − F(x)]`, i.e. `x ∈ S ⟺ r(x) = 0`. -/
theorem mem_viSol_iff_residual_eq_zero {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n))) (hCne : C.Nonempty) (hCc : IsClosed C)
    (hCcv : Convex ℝ C) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ viSol F C ↔ residual F C x = 0 := by sorry

end SolodovSvaiterVI.Alg21
