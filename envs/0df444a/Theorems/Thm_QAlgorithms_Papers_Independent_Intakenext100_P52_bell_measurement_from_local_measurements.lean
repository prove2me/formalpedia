-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_bell_measurement_from_local_measurements
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.bell_measurement_from_local_measurements
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:45:12.467355+00:00
-- url     : https://prove2.me/theorems/7cb66018-750a-438b-892e-88b762fbaf8a
-- title:
--   §7: Bell measurement from CX and local X/Z measurements
-- statement:
--   Use $|B_{cd}\rangle=(Z^cX^d\otimes I)(|00\rangle+|11\rangle)/\sqrt2$ and $|x_c\rangle=(|0\rangle+(-1)^c|1\rangle)/\sqrt2$. Then
--
--   $$ CX|B_{cd}\rangle=|x_c\rangle|d\rangle. $$
--
--   Consequently destructive Bell measurement, even with an arbitrary reference system, is exactly $CX$ followed by $X_1,Z_2$ measurement with outcome labels $c,d$. For Figure 12 start from $|\psi\rangle_1|0\rangle_2|+\rangle_3$, apply $CX_{3\to2}$ and $CX_{1\to2}$, then measure $X_1,Z_2$. The two entangling gates commute, and for every normalized input its output branch is $X^dZ^c|\psi\rangle/2$, with probability $1/4$. **Source correction:** the displayed intermediate labels on p.15 are interchanged relative to the p.2 Bell definition.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 15, §7: Bell measurement from CX and local X/Z measurements

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Bell measurement decomposition, PDF pp.15–16. Printed CX B_ij label map
is interchanged; changed to CX B_cd=|(-1)^c> |d>, consistent with p.2.
The bra identity holds with any reference, hence gives the full destructive
measurement instrument. Fig.12's two CXs share a target and commute. -/
theorem bell_measurement_from_local_measurements :
    (∀ c d : Bool, act cnot (sourceBellBasis c d) =
      tensorVec (equatorial 0 c) (ket d)) ∧
    (∀ (R : Type) [Fintype R] [DecidableEq R] (psi : Vec (QubitPair × R)) (c d : Bool),
      pairBra (sourceBellBasis c d) psi = localBellAnalysis c d psi) ∧
    cxWires (0 : Fin 3) 1 * cxWires (2 : Fin 3) 1 =
      cxWires (2 : Fin 3) 1 * cxWires (0 : Fin 3) 1 ∧
    (∀ (psi : Vec Bool), IsState psi → ∀ c d : Bool,
      figure12Branch c d psi =
        teleportContraction psi (finiteMaxEntangled Bool) (sourceBellBasis c d) ∧
      figure12Branch c d psi = (1 / 2 : ℂ) • act (pauliByproduct d c) psi ∧
      ‖figure12Branch c d psi‖ ^ 2 = (1 / 4 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
