-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P30_strictlyPositive_transpose_factorization
-- name    : QAlgorithms.Papers.Independent.Information100.P30.strictlyPositive_transpose_factorization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:20:38.475097+00:00
-- url     : https://prove2.me/theorems/55485235-317c-44a8-8e13-3cba0e113a52
-- title:
--   Transpose factorization for strictly positive qubit channels
-- statement:
--   Let $\Lambda$ be a complex-linear CPTP qubit map that sends every nonzero positive semidefinite matrix to a positive-definite matrix. Fix the computational basis and define its channel transpose by $\Lambda^{\mathsf T}(X)=\sum_i K_i^{\mathsf T}X\overline{K_i}$ for any Kraus representation. There exist invertible complex-linear maps $F,E$, with $F,E,F^{-1},E^{-1}$ all completely positive, such that
--
--   $$\Lambda^{\mathsf T}=F\circ\Lambda\circ E.$$
--
--   These filters need not preserve trace. This is invertible CP-filter equivalence and supplies the weaker positive-postmap/CP-prefilter criterion with no Kraus-rank restriction.
-- source:
--   Feasibility Ordering of Entanglement-Source Placement for Qubit Channels, arXiv:2609.18803v1, PDF p. 3, Proposition 1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P30

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Proposition 1 (PDF p.3, Eq.(21)): every strictly positive qubit channel is
equivalent to its channel transpose under invertible CP filters whose inverses are CP.
The witnesses are superoperators and need not preserve trace; no Kraus-rank bound is imposed. -/
theorem strictlyPositive_transpose_factorization (F : MatrixMap Bool Bool)
    (hF : IsQubitChannel F) (hstrict : IsStrictlyPositive F) :
    ∃ P Q : Matrix Bool Bool ℂ ≃ₗ[ℂ] Matrix Bool Bool ℂ,
      Entanglement.IsCompletelyPositive P.toLinearMap ∧
      Entanglement.IsCompletelyPositive P.symm.toLinearMap ∧
      Entanglement.IsCompletelyPositive Q.toLinearMap ∧
      Entanglement.IsCompletelyPositive Q.symm.toLinearMap ∧
      channelTranspose F = P.toLinearMap.comp (F.comp Q.toLinearMap) := by sorry

end QAlgorithms.Papers.Independent.Information100.P30

end
