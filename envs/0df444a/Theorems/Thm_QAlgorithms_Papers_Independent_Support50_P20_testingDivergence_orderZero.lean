-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P20_testingDivergence_orderZero
-- name    : QAlgorithms.Papers.Independent.Support50.P20.testingDivergence_orderZero
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:31:09.943202+00:00
-- url     : https://prove2.me/theorems/3ce66135-6c2f-4db4-aba4-6be27749bc78
-- title:
--   Zero-error testing divergence is order-zero Renyi divergence
-- statement:
--   Let $\rho$ and $\sigma$ be normalized positive trace-class operators on the same complex Hilbert space. Let $\Pi_\rho$ be the orthogonal projection onto the closed support of $\rho$, equivalently the orthogonal complement of its kernel. Define $D_H^\epsilon$ by the binary testing infimum in (1), using base-two logarithms and the convention $-\log_2 0=+\infty$. Then
--
--   $$
--   D_H^0(\rho\|\sigma)=D_0(\rho\|\sigma)=-\log_2\operatorname{Tr}(\Pi_\rho\sigma).
--   $$
--
--   This identity identifies exact acceptance in hypothesis testing with the order-zero Renyi divergence, including state pairs with orthogonal supports. Neither invertibility nor support inclusion is assumed.
-- source:
--   One-Shot Classical-Quantum Capacity and Hypothesis Testing, arXiv:1007.5456v3, PDF p. 2, Unnumbered: zero-error testing divergence equals order-zero Renyi relative entropy

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

/-- PDF p.2, paragraph after (1): zero-error testing divergence equals
order-zero Renyi divergence, including orthogonal supports and infinity. -/
theorem testingDivergence_orderZero {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : State b) :
    hilbertTestingDivergence b 0 rho.val.val sigma.val.val =
      orderZeroDivergence b rho.val.val sigma.val.val := by sorry

end QAlgorithms.Papers.Independent.Support50.P20

end
