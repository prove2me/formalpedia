-- Prove2me | Theorems.Thm_ProjNewton_Superlinear_proposition1
-- name    : ProjNewton.Superlinear.proposition1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:30:18.609883+00:00
-- url     : https://prove2.me/theorems/bed4ceb1-cdb1-43c5-9615-e181a223047f
-- title:
--   Proposition 1 — critical points and descent along the projected arc
-- statement:
--   Let $n\ge1$, let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable, let $x\ge0$, and let $D$ be symmetric positive definite and diagonal with respect to $I^+(x)$. Define $x(a)=[x-aD\nabla f(x)]^+$ for $a\ge0$. Then:
--
--   $$x\text{ is critical}\quad\Longleftrightarrow\quad x(a)=x\text{ for every }a\ge0.$$
--
--   If $x$ is not critical, some $\bar a>0$ satisfies $f(x(a))<f(x)$ for every $0<a\le\bar a$. This links the orthant first-order condition to the projected arc and supplies local descent.
--
--   **Formalization Note** Feasibility, the paper's standing $C^1$ assumption and $n\ge1$ are explicit. The matrix condition zeroes rows indexed by $I^+(x)$; symmetry supplies the matching columns.
-- source:
--   Bertsekas, Projected Newton Methods for Optimization Problems with Simple Constraints, SIAM J. Control Optim. 20(2) (1982), p. 226, Proposition 1

import Mathlib
import Definitions.Def_ProjNewton_Superlinear_Algorithm

namespace ProjNewton.Superlinear

open Matrix Filter Topology

/-- Bertsekas (1982), Proposition 1, p. 226. -/
theorem proposition1 {n : ℕ} (hn : 0 < n) (f : Vec n → ℝ)
    (hf : ContDiff ℝ 1 f) (x : Vec n) (hx : x ∈ orthant n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (hdiag : DiagonalWrt D (Iplus f x)) :
    (IsCritical f x ↔ ∀ a : ℝ, 0 ≤ a → arc f D x a = x) ∧
    (¬ IsCritical f x → ∃ abar : ℝ, 0 < abar ∧
      ∀ a ∈ Set.Ioc (0 : ℝ) abar, f (arc f D x a) < f x) := by sorry

end ProjNewton.Superlinear
