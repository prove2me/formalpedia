-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_nonEntangling_superactivation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.nonEntangling_superactivation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:37:55.934314+00:00
-- url     : https://prove2.me/theorems/aff754d1-bb4a-43f6-a27f-b38566d1bcda
-- title:
--   Theorem 11: superactivation of a non-entangling channel
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. A non-entangling map is completely positive and preserves the full separable positive cone. A channel is also trace preserving. There exists a channel $\Lambda$ on two qubits that is non-entangling, while
--
--   $$\Lambda\otimes\Lambda\text{ is not non-entangling across }AA^{\prime}:BB^{\prime}.$$
--
--   Thus this operation class is not closed under tensor products.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 15, Theorem 11

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P19

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P19

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P19 (Bip)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

/-- Theorem 11, PDF pp.15-16: a two-qubit channel is non-entangling,
but its tensor square generates entanglement across AA':BB'. -/
theorem nonEntangling_superactivation :
    ∃ L : Superop (Fin 2 × Fin 2) (Fin 2 × Fin 2),
      IsChannel L ∧ NE L ∧ ¬ NE (tensorMaps L L) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
