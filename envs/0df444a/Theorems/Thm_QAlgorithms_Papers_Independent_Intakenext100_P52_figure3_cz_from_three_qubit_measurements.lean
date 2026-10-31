-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_figure3_cz_from_three_qubit_measurements
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.figure3_cz_from_three_qubit_measurements
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:34:23.511328+00:00
-- url     : https://prove2.me/theorems/755cf5c5-05d3-4dd0-963c-1fd4cdae76ba
-- title:
--   Figure 3: CZ from two three-qubit measurements
-- statement:
--   Prepare an arbitrary normalized input on qubits $1,2$ and normalized $H$-bonds $CZ|++\rangle$ on pairs $34,57,68$. On $135$ and $246$ measure in the eight normalized three-qubit GHZ kets obtained from the pairs $000/111$, $001/110$, $010/101$, $100/011$ by choosing the plus or minus sign. These kets form an orthonormal basis. There is one Pauli correction rule $s\mapsto(P_1(s),P_2(s))$, fixed before the input, such that the actual branch vector $b_s$ on outputs $7,8$ satisfies
--
--   $$ |b_s\rangle\langle b_s|=\|b_s\|^2\,|\chi_s\rangle\langle\chi_s|,\quad |\chi_s\rangle=(P_1(s)\otimes P_2(s))(H\otimes H)CZ|\psi\rangle. $$
--
--   This gives the conditional quantum output on every nonzero branch, and also includes zero branches without division. The $H$-bonds are resources; the two $H$ operators in the output are Hadamard gates.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 4, Figure 3: CZ from two three-qubit measurements

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Fig.3, PDF p.4: H-bonds are resource states; the two H factors in the
output formula are actual gates. The correction is chosen before the unknown
input. Homogeneous density equality handles any zero branch without division. -/
theorem figure3_cz_from_three_qubit_measurements :
    Orthonormal ℂ (fun a : Fin 4 × Bool => threeQubitBellKet a.1 a.2) ∧
    ∃ correction : ((Fin 4 × Bool) × (Fin 4 × Bool)) → (QubitPair × QubitPair),
      ∀ (psi : Vec QubitPair), IsState psi → ∀ a b : Fin 4 × Bool,
        let f := correction (a,b)
        let v := figure3Branch a b psi
        pureDensity v = (‖v‖ ^ 2 : ℝ) • pureDensity
          (act (Matrix.kronecker (pauliByproduct f.1.1 f.1.2) (pauliByproduct f.2.1 f.2.2) *
            Matrix.kronecker hadamard hadamard * controlled pauliZ) psi) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
