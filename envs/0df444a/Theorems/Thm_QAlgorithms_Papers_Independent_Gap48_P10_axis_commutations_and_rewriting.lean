-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_axis_commutations_and_rewriting
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.axis_commutations_and_rewriting
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:32:12.63565+00:00
-- url     : https://prove2.me/theorems/62af026a-2fc5-460a-9cea-a8bd84def337
-- title:
--   §8.2 unnumbered: axis commutations and rewriting
-- statement:
--   Let $E=HS^3\omega^3$, $T_x=ETE^2$, $T_y=E^2TE$ and $T_z=T$. Then
--
--   $$
--   ET_x=T_yE,\qquad ET_y=T_zE,\qquad ET_z=T_xE.
--   $$
--   Every E–T normal expression $M$ therefore has a unique axis expression $T_{r_1}\cdots T_{r_n}C$ of the same absolute operator and with $n$ equal to its displayed $T$-count, where $r_i\in\{x,y,z\}$ and adjacent axes are distinct.
--
--   Nonadjacent repetitions of an axis are allowed, and the empty axis list is allowed. This is the precise reading fixed by Proposition 8.2.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 11, §8.2 unnumbered: axis commutations and rewriting

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Section 8.2 commutations and rewriting, PDF p.11. "No repeated symbol"
means adjacent distinctness, as specified by Proposition 8.2 on p.12. -/
theorem axis_commutations_and_rewriting :
    cliffordE.val * axisTGate 0 = axisTGate 1 * cliffordE.val ∧
    cliffordE.val * axisTGate 1 = axisTGate 2 * cliffordE.val ∧
    cliffordE.val * axisTGate 2 = axisTGate 0 * cliffordE.val ∧
    ∀ M : NormalForm, ∃! A : AxisForm,
      axisValue A = normalValue cliffordE cliffordE2 M ∧ A.axes.length = normalTCount M := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
