-- Prove2me | Theorems.Thm_PCSPBLPAff_Symmetric_maxSupport_exists
-- name    : PCSPBLPAff.Symmetric.maxSupport_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:08.53146+00:00
-- url     : https://prove2.me/theorems/66d7c776-097d-442e-a94f-f87406cec7e1
-- title:
--   Footnote 1, §2.3, p. 5 — a feasible LP_Q(X, A) has a solution of maximal support (a relative interior point)
-- statement:
--   Let $X$ be an instance and $\mathbf A$ a structure on a finite domain $A$. If the Basic LP $\mathrm{LP}_{\mathbb Q}(X,\mathbf A)$ has a solution, then it has a solution $(w^\ast,p^\ast)$ at which each coordinate is nonzero if and only if it is nonzero at some point of the polytope:
--   $$
--   \mathrm{LP}_{\mathbb Q}(X,\mathbf A)\neq\emptyset\ \Longrightarrow\ \exists (w^\ast,p^\ast)\in\mathrm{LP}_{\mathbb Q}(X,\mathbf A)\ \ \forall (w,p)\in\mathrm{LP}_{\mathbb Q}(X,\mathbf A):\ \operatorname{supp}(w,p)\subseteq\operatorname{supp}(w^\ast,p^\ast).
--   $$
--
--   This makes step 1 of the BLP+Affine algorithm well defined: a relative interior point exists whenever the LP is feasible, and the algorithm's refinement only uses its zero set.
--
--   **Formalization Note** All coordinates are non-negative, so "positive" and "nonzero" coincide.
-- source:
--   arXiv:1907.04383v3, §2.3, p. 5, last sentences before §2.3's affine relaxation, and footnote 1

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

namespace PCSPBLPAff.Symmetric

/-- Footnote 1 / §2.3 (p. 5): if `LP_ℚ(X, 𝔸)` is feasible, it has a solution whose support
contains the support of every solution (a point at which each coordinate is positive iff it is
positive at some point of the polytope). -/
theorem maxSupport_exists {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (X : Instance τ ar) (𝔸 : RelStruct τ ar A) (w : Fin X.n → A → ℚ)
    (p : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ) (h : IsLPSol X 𝔸 w p) :
    ∃ (w' : Fin X.n → A → ℚ) (p' : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ),
      IsMaxSupportLPSol X 𝔸 w' p' := by sorry

end PCSPBLPAff.Symmetric
