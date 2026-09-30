-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_span_rank_stability_iff
-- name    : WeierstrassEllipticZeta.finite_span_rank_stability_iff
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-13T03:00:19.672389+00:00
-- url     : https://prove2.me/theorems/83670126-2e3e-4b61-99a3-c776f1eecbda
-- title:
--   Finite spans stabilize exactly when their ranks stabilize
-- statement:
--   Let $K$ be a field, $V$ a $K$-vector space, $f:\iota\to V$ an indexed family of vectors, and $S,B\subseteq\iota$ finite sets. Then
--   $$
--   \bigl(\forall b\in B,\ f(b)\in\operatorname{span}_K f(S)\bigr)
--   \quad\Longleftrightarrow\quad
--   \dim_K\operatorname{span}_K f(S\cup B)=\dim_K\operatorname{span}_K f(S).
--   $$
--   The dimensions refer to the finite spans of the specified vectors. The ambient vector space need not be finite-dimensional. Neither linear independence nor distinctness of the vectors is assumed; empty sets are allowed.
-- source:
--   Derived finite-rank criterion for the frontier https://prove2.me/theorems/43f9e206-8378-4242-a2c1-283b4fdbfb45. The mission setting is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The supporting equivalence uses finite generation of spans and equality of nested subspaces of equal finite dimension in Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. The uniform geometric bound remains open.

import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section

theorem WeierstrassEllipticZeta.finite_span_rank_stability_iff
    (K V ι : Type*) [Field K] [AddCommGroup V] [Module K V]
    [DecidableEq ι] (f : ι → V) (S B : Finset ι) :
    (∀ b ∈ B, f b ∈ Submodule.span K (f '' (S : Set ι))) ↔
      Module.finrank K (Submodule.span K (f '' ((S ∪ B : Finset ι) : Set ι))) =
        Module.finrank K (Submodule.span K (f '' (S : Set ι))) := by sorry
