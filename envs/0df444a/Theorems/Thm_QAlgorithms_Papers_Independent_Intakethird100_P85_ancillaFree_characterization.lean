-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P85_ancillaFree_characterization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P85.ancillaFree_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:13:55.444381+00:00
-- url     : https://prove2.me/theorems/cc9d8ecc-1ace-47f5-b67d-f822d2307e5d
-- title:
--   Corollary 2: full ancilla-free determinant characterization
-- statement:
--   Let $U$ be a unitary operator on $n\ge0$ qubits. Put $R=\mathbb Z[1/\sqrt2,i]$ and $\omega=e^{i\pi/4}$. Then $U$ is exactly representable by an ancilla-free Clifford+T circuit if and only if every entry belongs to $R$ and
--
--   $$
--   \det U\in
--   \begin{cases}
--   \{1\},&n\ge4,\\
--   \{-1,1\},&n=3,\\
--   \{i,-1,-i,1\},&n=2,\\
--   \{\omega,i,\omega^3,-1,\omega^5,-i,\omega^7,1\},&n\le1.
--   \end{cases}
--   $$
--
--   The gate set includes the scalar $\omega$ and preserves absolute phase. The final regime is retained even though the entry and unitary conditions already imply it. This characterizes the ancilla-free group in every qubit dimension.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, PDF p. 6, Corollary 2: full ancilla-free determinant characterization

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P85

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P85

open scoped Classical BigOperators

open QAlgorithms

open QAlgorithms.Papers.Independent.Gap48.P10
  (InZomega InDomega Residue bits residue residueMultiply Reducible)

open QAlgorithms.Papers.Independent.Support21.P13
  (synthesisRing integralRing coordinateValue HTLetter htWordMatrix EntriesInRing cliffordTLibrary)

local notation "omega" => QAlgorithms.gateT true true

local notation "sqrtTwo" => ((Real.sqrt 2 : ℝ) : ℂ)

/-- Corollary 2, PDF p.6: all four exact ancilla-free determinant regimes. -/
theorem ancillaFree_characterization (n : ℕ) (U : Matrix (Qubits n) (Qubits n) ℂ)
    (unitary : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    (∃ c : Circuit gateSet n, c.unitary = U) ↔
      EntriesInRing U ∧
      (4 ≤ n → U.det = 1) ∧
      (n = 3 → U.det ∈ ({-1, 1} : Set ℂ)) ∧
      (n = 2 → U.det ∈ ({Complex.I, -1, -Complex.I, 1} : Set ℂ)) ∧
      (n ≤ 1 → U.det ∈ ({omega, Complex.I, omega ^ 3, -1,
        omega ^ 5, -Complex.I, omega ^ 7, 1} : Set ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P85

end
