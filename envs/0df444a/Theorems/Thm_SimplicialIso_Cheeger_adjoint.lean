-- Prove2me | Theorems.Thm_SimplicialIso_Cheeger_adjoint
-- name    : SimplicialIso.Cheeger.adjoint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:15.958183+00:00
-- url     : https://prove2.me/theorems/4afd2cbc-dab8-457c-9bea-61fef8195e53
-- title:
--   p. 6 — ∂*_d is the adjoint of ∂_d: ⟨∂_d g, f⟩ = ⟨g, ∂*_d f⟩
-- statement:
--   Let $X$ be a finite $d$-dimensional simplicial complex with a complete skeleton, $d\ge1$. With respect to the inner product (2.1), the co-boundary operator $\partial_d^*:\Omega^{d-1}\to\Omega^d$, $(\partial_d^*f)(\sigma)=\sum_{i=0}^d(-1)^i f(\sigma\setminus\sigma_i)$, is the adjoint of the boundary operator $\partial_d$: for all $f\in\Omega^{d-1}$ and $g\in\Omega^d$,
--   $$\langle \partial_d g, f\rangle=\langle g,\partial_d^* f\rangle .$$
--   In particular $\langle\Delta^+f,f\rangle=\langle\partial_d^*f,\partial_d^*f\rangle$, the equality used in (4.2).
--
--   **Formalization Note.** Both operators are defined by their explicit formulas, so the adjointness is a statement, not a definition. The inner product on $\Omega^d$ sums over all $(d+1)$-element sets; since $\partial_d^*f$ vanishes off the $d$-cells, this is the sum over $X^d$ of (2.1).
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, p. 6, §2: "The adjoint of ∂_j w.r.t. the inner product (2.1) is the co-boundary operator ∂*_j" (case j = d)

import Mathlib
import Definitions.Def_SimplicialIso_Cheeger_Setting

namespace SimplicialIso.Cheeger

theorem adjoint (n d : ℕ) (hd : 1 ≤ d) (X : Complex n d) (g : Form n (d + 1)) (f : Form n d) :
    inner ℝ (bdTop X g) f = inner ℝ g (cobdTop X f) := by sorry

end SimplicialIso.Cheeger
