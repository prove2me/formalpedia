-- Prove2me | Theorems.Thm_StabGen_RKHS_reproducing_eval_bound
-- name    : StabGen.RKHS.reproducing_eval_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:37:54.816003+00:00
-- url     : https://prove2.me/theorems/9bb5b4bf-8522-436d-b07e-ab9ea8f9eda1
-- title:
--   Equation (25) — RKHS point-evaluation bound
-- statement:
--   Let $H$ be a real reproducing kernel Hilbert space with kernel $K$, evaluation $f(x)$ and feature representative $\Phi(x)=K(x,\cdot)$. Then every $f\in H$ and $x\in X$ satisfy
--   $$|f(x)|\le\|f\|_K\sqrt{K(x,x)}.$$
--
--   This bound converts a distance in the RKHS norm into a pointwise prediction bound.
--
--   **Formalization Note** The published RKHS definition identifies $f(x)$ with $\langle f,\Phi(x)\rangle$ and $K(x,x)$ with $\|\Phi(x)\|^2$.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 514 (PDF p. 16), Eq. (25), https://jmlr.org/papers/v2/bousquet02a.html

import Mathlib
import Definitions.Def_FoundationsML_Stability_IsRKHSOf

namespace StabGen.RKHS

open FoundationsML.Stability

/-- Equation (25), p. 514: the point-evaluation bound from the reproducing property. -/
theorem reproducing_eval_bound {X H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : X → X → ℝ) (Φ : X → H) (ev : H → X → ℝ)
    (hRKHS : IsRKHSOf K Φ ev) (f : H) (x : X) :
    |ev f x| ≤ ‖f‖ * Real.sqrt (K x x) := by sorry

end StabGen.RKHS
