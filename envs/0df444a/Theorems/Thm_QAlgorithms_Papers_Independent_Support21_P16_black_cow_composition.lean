-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P16_black_cow_composition
-- name    : QAlgorithms.Papers.Independent.Support21.P16.black_cow_composition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:42:29.73161+00:00
-- url     : https://prove2.me/theorems/e8cad2d8-09c9-4b7c-a39f-fc472c4bbbbe
-- title:
--   Black Cow coefficients multiply under composition
-- statement:
--   Let $d>0$ and $1\le N<M<R$ be integers. Let $T$ map the $N$-particle Bose input algebra to $M$ particles, and $S$ map the $M$-particle Bose input algebra to $R$ particles. Assume each map is complex-linear, completely positive, trace-preserving on its input corner, covariant under $U(d)$, and has Bose-supported output. Both are canonically zero-extended. For a map $V$ from $a$ to $b$ systems, call a real $g$ a Black Cow coefficient when $R_b(V(A))=gR_a(A)+(1-g)\operatorname{tr}(A)I/d$ for every Bose-supported $A$, where $R_k$ retains the first site. Such coefficients exist for $T$ and $S$. For every choice $g_T,g_S$ satisfying those identities,
--   $$
--   R_R(S(T(A)))=g_Sg_T R_N(A)+(1-g_Sg_T)\operatorname{tr}(A)\frac{I}{d}
--   $$
--   for every Bose-supported $N$-particle operator $A$. The composite is also admissible, covariant and Bose-output.
--
--   This is multiplicativity for cloning in stages without assuming that the intermediate output is a product state. It remains meaningful when $d=1$ and numerical coefficients are nonunique.
-- source:
--   Optimal Cloning of Pure States, arXiv:quant-ph/9804001v1, PDF p. 7, black-cow-composition

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support21.P16

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector powerVector IsCloningCovariant haarAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Support21.P16.unitaryMeasurable

/-- PDF p.7, cloning-in-stages corollary: the intermediate input may be
correlated. Equation (3.7), on the whole Bose algebra, gives multiplication. -/
theorem black_cow_composition (d N M R : ℕ) (hd : 0 < d) (hN : 1 ≤ N)
    (hNM : N < M) (hMR : M < R) (T : CloneMap d N M) (S : CloneMap d M R)
    (hT : IsBoseInputChannel T) (hS : IsBoseInputChannel S) (hBT : HasBoseOutput T)
    (hBS : HasBoseOutput S) (hCT : IsCloningCovariant T) (hCS : IsCloningCovariant S) :
    IsBoseInputChannel (S ∘ T) ∧ HasBoseOutput (S ∘ T) ∧ IsCloningCovariant (S ∘ T) ∧
    (∃ gT gS : ℝ, HasBlackCowCoefficient hN (by omega) T gT ∧
      HasBlackCowCoefficient (by omega) (by omega) S gS) ∧
    (∀ gT gS : ℝ, HasBlackCowCoefficient hN (by omega) T gT →
      HasBlackCowCoefficient (by omega) (by omega) S gS →
      HasBlackCowCoefficient hN (by omega) (S ∘ T) (gS * gT)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P16

end
