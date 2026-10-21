-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P16_black_cow
-- name    : QAlgorithms.Papers.Independent.Support21.P16.black_cow
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:41:50.467026+00:00
-- url     : https://prove2.me/theorems/89fc8997-6020-4799-a034-e8df6d64b8d0
-- title:
--   The Black Cow marginal identity on the full Bose algebra
-- statement:
--   Let $d>0$ and $1\le N<M$ be integers. Let $T$ be a complex-linear completely positive trace-preserving map from the $N$-particle Bose operator algebra to the full $M$-particle algebra, canonically zero-extended to ambient inputs. Assume that its outputs are Bose-supported and that it is covariant under every $U\in U(d)$. Let $R_k$ trace out all but the first site of a $k$-particle operator, and put $\tau_1=I/d$. There is a real scalar $\gamma$ such that for every Bose-supported operator $A$,
--   $$
--   R_M(T(A))=\gamma R_N(A)+(1-\gamma)\operatorname{tr}(A)\tau_1.
--   $$
--   For every unit $\phi\in\mathbb C^d$, with $\sigma=|\phi\rangle\langle\phi|$, the same scalar satisfies $R_M(T(\sigma^{\otimes N}))=\gamma\sigma+(1-\gamma)\tau_1$.
--
--   This extends the product-input marginal identity to arbitrary correlated Bose operators. The coefficient is relational: no unjustified interval restriction or uniqueness at $d=1$ is imposed.
-- source:
--   Optimal Cloning of Pure States, arXiv:quant-ph/9804001v1, PDF p. 7, black-cow

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

/-- PDF pp.6–7 Eqs.(3.6)–(3.7): both symmetry hypotheses are needed here.
A single REAL coefficient works on all Bose operators, with their trace;
at d=1 it is deliberately not claimed to be numerically identifiable. -/
theorem black_cow (d N M : ℕ) (hd : 0 < d) (hN : 1 ≤ N) (hNM : N < M)
    (T : CloneMap d N M) (hT : IsBoseInputChannel T) (hB : HasBoseOutput T)
    (hC : IsCloningCovariant T) :
    ∃ gamma : ℝ, HasBlackCowCoefficient hN (by omega) T gamma ∧
      ∀ phi : EuclideanSpace ℂ (Fin d), ‖phi‖ = 1 →
        oneSite (by omega) (T (QAlgorithms.pureDensity (coherentTensor N phi))) =
          (gamma : ℂ) • QAlgorithms.pureDensity phi +
            ((1 - gamma : ℝ) : ℂ) • oneMixed d := by sorry

end QAlgorithms.Papers.Independent.Support21.P16

end
