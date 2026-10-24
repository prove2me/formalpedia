-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P20_testingDivergence_relativeEntropyBound
-- name    : QAlgorithms.Papers.Independent.Support50.P20.testingDivergence_relativeEntropyBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:33:16.81058+00:00
-- url     : https://prove2.me/theorems/a5678c7b-8fad-428f-821b-591fe4de33c8
-- title:
--   Testing divergence bounded by Umegaki relative entropy
-- statement:
--   Let $\rho,\sigma$ be arbitrary normalized positive trace-class operators on the same complex Hilbert space, and let $0\le\epsilon<1$. Write $D(\rho\|\sigma)$ for the extended Umegaki relative entropy in bits and $H_b(t)=-t\log_2t-(1-t)\log_2(1-t)$ for binary entropy, with $0\log_2 0=0$. Then
--
--   $$
--   D_H^\epsilon(\rho\|\sigma)\le\frac{D(\rho\|\sigma)+H_b(\epsilon)}{1-\epsilon}.
--   $$
--
--   This comparison relates the testing information to ordinary relative entropy. The whole numerator is divided by the positive number $1-\epsilon$; no invertibility or finite-relative-entropy condition is imposed. Infinite values are retained.
-- source:
--   One-Shot Classical-Quantum Capacity and Hypothesis Testing, arXiv:1007.5456v3, PDF p. 2, Property 3, (2): testing divergence bounded by ordinary relative entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P20

noncomputable section

open Filter

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P20

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace State)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.2, Property 3, (2): the WHOLE numerator is divided by 1-epsilon.
Infinite relative entropy is retained; this denominator is strictly positive. -/
theorem testingDivergence_relativeEntropyBound {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : State b) (epsilon : ℝ) (hZero : 0 ≤ epsilon) (hOne : epsilon < 1) :
    hilbertTestingDivergence b epsilon rho.val.val sigma.val.val ≤
      ((traceClassRelativeEntropyBits rho sigma : EReal) + (QAlgorithms.binEntropy2 epsilon : ℝ)) /
        ((1 - epsilon : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Support50.P20

end
