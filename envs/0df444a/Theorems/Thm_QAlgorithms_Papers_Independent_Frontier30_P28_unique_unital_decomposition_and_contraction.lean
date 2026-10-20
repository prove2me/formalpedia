-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P28_unique_unital_decomposition_and_contraction
-- name    : QAlgorithms.Papers.Independent.Frontier30.P28.unique_unital_decomposition_and_contraction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:19:34.539488+00:00
-- url     : https://prove2.me/theorems/4268f44a-d646-46a4-a3bc-75fe5cc19db9
-- title:
--   Unique unital decomposition and conditional complex-traceless contractivity
-- statement:
--   Let $n\ge1$, and let $T:M_n\to M_n$ be any trace-preserving complex-linear map for the ordinary trace. Set
--
--   $$
--   N=\frac{T(I_n)-I_n}{n},\qquad
--   T_1(A)=T(A)-N\operatorname{tr}A.
--   $$
--
--   Then $\operatorname{tr}N=0$, $T_1$ is unital and trace preserving, and $T(A)=N\operatorname{tr}A+T_1(A)$ for every $A$. This pair is unique among all traceless matrices $N'$ and unital trace-preserving complex-linear maps $U$ with $T(A)=N'\operatorname{tr}A+U(A)$ for every $A$.
--
--   If the constructed $T_1$ is positive, then for every $1\le p\le\infty$,
--
--   $$
--   \bigl\|T|_{\{A:\operatorname{tr}A=0\}}\bigr\|_{p-p}\le1.
--   $$
--
--   The last domain includes all complex traceless matrices, without a Hermitian restriction. No positivity is required for the decomposition itself. This separates the nonunital correction from the unital part and identifies a sufficient condition for unrestricted traceless contraction.
-- source:
--   Contractivity of positive and trace preserving maps under $L_p$ norms, arXiv:math-ph/0601063v1, PDF p. 5, §III, concluding paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P28

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier30.P28

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P11 (IsUnital)

/-- Unnumbered decomposition and conditional contractivity, source PDF p.5.
No positivity is assumed for the decomposition. Its restricted contraction
conclusion concerns all complex traceless matrices and requires positivity
of the constructed unital part, not of a freely supplied substitute. -/
theorem unique_unital_decomposition_and_contraction
    (n : ℕ) (hn : 0 < n) (T : Lin n n)
    (htrace : TracePreserving T) :
    let N := nonunitalOffset T
    let U := unitalPart T
    N.trace = 0 ∧ IsUnital U ∧ TracePreserving U ∧
    (∀ A : M n, T A = A.trace • N + U A) ∧
    (∀ (Nother : M n) (Uother : Lin n n),
      Nother.trace = 0 → IsUnital Uother → TracePreserving Uother →
      (∀ A : M n, T A = A.trace • Nother + Uother A) →
      Nother = N ∧ Uother = U) ∧
    (IsPositiveMap U → ∀ p : ℝ≥0∞, 1 ≤ p →
      restrictedPNorm p T (fun A => A.trace = 0) ≤ 1) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P28

end
