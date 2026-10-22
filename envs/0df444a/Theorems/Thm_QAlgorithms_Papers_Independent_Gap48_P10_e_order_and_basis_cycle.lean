-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_e_order_and_basis_cycle
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.e_order_and_basis_cycle
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:31:12.343654+00:00
-- url     : https://prove2.me/theorems/0b35a26b-f3c4-4a3f-b4c1-993c01479633
-- title:
--   §8.1 unnumbered: E order and basis cycle
-- statement:
--   Let $E=HS^3\omega^3$, where $\omega^3$ denotes the scalar gate $\omega^3 I$. With the usual ordered Pauli matrices $X,Y,Z$,
--
--   $$
--   E^3=I,\qquad EXE^\dagger=Y,\qquad EYE^\dagger=Z,\qquad EZE^\dagger=X.
--   $$
--   These identities include the exact scalar phase of $E$ and specify its orientation as a cyclic basis change.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 11, §8.1 unnumbered: E order and basis cycle

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Section 8.1 displayed properties, PDF p.11. E includes omega^3, so the order
identity is exact and the X,Y,Z cycle has the source's orientation. -/
theorem e_order_and_basis_cycle :
    cliffordE.val ^ 3 = 1 ∧
    cliffordE.val * QAlgorithms.pauliX * star cliffordE.val = QAlgorithms.pauliY ∧
    cliffordE.val * QAlgorithms.pauliY * star cliffordE.val = QAlgorithms.pauliZ ∧
    cliffordE.val * QAlgorithms.pauliZ * star cliffordE.val = QAlgorithms.pauliX := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
