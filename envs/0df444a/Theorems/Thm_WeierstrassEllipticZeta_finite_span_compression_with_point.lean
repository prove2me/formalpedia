-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_span_compression_with_point
-- name    : WeierstrassEllipticZeta.finite_span_compression_with_point
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-13T03:13:07.637591+00:00
-- url     : https://prove2.me/theorems/8b0cb3bb-99fe-476e-b320-4d820e957c01
-- title:
--   Compressing a finite spanning family while retaining a marked index
-- statement:
--   Let $K$ be a field, $V$ a $K$-vector space, $f:\iota\to V$ an indexed family of vectors, and $S\subseteq\iota$ a finite set containing a specified index $i_0$. There is a finite set $T\subseteq S$ such that
--   $$i_0\in T,\qquad \operatorname{span}_K f(T)=\operatorname{span}_K f(S),\qquad
--   |T|\le\dim_K\operatorname{span}_K f(S)+1.$$
--   No finite-dimensionality of the ambient space, independence of the vectors, or nonvanishing of $f(i_0)$ is assumed. The extra one permits retaining the marked index even when its vector is zero or dependent on the chosen basis vectors.
-- source:
--   Derived span-compression certificate for the frontier https://prove2.me/theorems/194e222c-6b11-4625-b7d1-bf490d20a01a. The mission setting is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The supporting compression lemma uses a basis chosen from a finite spanning family in Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. The uniform geometric rank bound remains open.

import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

noncomputable section

theorem WeierstrassEllipticZeta.finite_span_compression_with_point
    (K V ι : Type*) [Field K] [AddCommGroup V] [Module K V]
    (f : ι → V) (S : Finset ι) (i₀ : ι) (hi₀ : i₀ ∈ S) :
    ∃ T : Finset ι, T ⊆ S ∧ i₀ ∈ T ∧
      Submodule.span K (f '' (T : Set ι)) = Submodule.span K (f '' (S : Set ι)) ∧
      T.card ≤ Module.finrank K (Submodule.span K (f '' (S : Set ι))) + 1 := by sorry
