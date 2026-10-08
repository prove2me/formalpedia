-- Prove2me | Theorems.Thm_PCSPBLPAff_Symmetric_completeness
-- name    : PCSPBLPAff.Symmetric.completeness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:10.386671+00:00
-- url     : https://prove2.me/theorems/b6bb254f-211e-4a46-9b2d-1eb73ef1fc7f
-- title:
--   Proof of Theorem 2, p. 6 — if X is satisfiable in A, the BLP+Affine algorithm accepts
-- statement:
--   Let $\mathbf A$ be a structure on a finite domain $A$ and $X$ an instance of the same signature. If $X$ is satisfiable in $\mathbf A$, then the BLP+Affine algorithm accepts $X$:
--   $$
--   X \text{ satisfiable in } \mathbf A\ \Longrightarrow\ \mathrm{LP}_{\mathbb Q}(X,\mathbf A) \text{ has a maximal-support solution } (w,p) \text{ and } \mathrm{Aff}'_{\mathbb Z}(X,\mathbf A)\neq\emptyset.
--   $$
--
--   This is the completeness half of Definition 1, and it holds for every template: no polymorphism is involved.
-- source:
--   arXiv:1907.04383v3, proof of Theorem 2, p. 6, first paragraph

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

namespace PCSPBLPAff.Symmetric

/-- Proof of Theorem 2, p. 6, first paragraph: if `X` is satisfiable in `𝔸`, the BLP+Affine
algorithm accepts `X`. -/
theorem completeness {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (𝔸 : RelStruct τ ar A) (X : Instance τ ar) (hX : SatIn X 𝔸) :
    Accepts 𝔸 X := by sorry

end PCSPBLPAff.Symmetric
