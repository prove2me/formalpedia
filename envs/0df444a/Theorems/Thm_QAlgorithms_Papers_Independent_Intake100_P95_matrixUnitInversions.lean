-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_matrixUnitInversions
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.matrixUnitInversions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:55:29.420137+00:00
-- url     : https://prove2.me/theorems/e2c34e10-506d-4228-b6a1-8cf5474a9cba
-- title:
--   Torus, single-spin, and joint-spin inversion of matrix units
-- statement:
--   Let $n\ge1$ and let $E_{ij}$ be an off-diagonal matrix unit on the $n$-qubit computational basis, indexed by distinct $n$-bit strings $i,j$. There exist real torus angles $\theta_k$ such that
--
--   $$\sum_k\theta_k=0,\qquad\theta_i-\theta_j\in\pi+2\pi\mathbb Z,\qquad\operatorname{Ad}_{\operatorname{diag}(e^{-i\theta_k})}(E_{ij})=-E_{ij}.$$
--
--   There also exist one qubit and a real z-rotation angle on that qubit alone that sign-invert $E_{ij}$. If a joint z-rotation with the same angle on every qubit sign-inverts $E_{ij}$, then $i$ and $j$ have different Hamming weights. The last assertion is stated only as a necessary condition. These bit strings represent the paper's one-based indices after subtracting one, with leading zeroes retained.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 9, Proposition 1: individual and joint inversion of matrix units

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- Proposition 1(1)–(3), PDF p.9. Indices are already reduced by one.
The torus angles sum to zero. The final clause remains necessary only. -/
theorem matrixUnitInversions {n : ℕ} (hn : 0 < n)
    (i j : QAlgorithms.Qubits n) (hij : i ≠ j) :
    (∃ theta : QAlgorithms.Qubits n → ℝ,
      (∑ k, theta k) = 0 ∧ OddPi (theta i - theta j) ∧
      adjointConjugation (torus theta) (Matrix.single i j (1 : ℂ)) = -Matrix.single i j (1 : ℂ)) ∧
    (∃ (l : Fin n) (phi : ℝ),
      adjointConjugation (individualZRotation (fun k => if k = l then phi else 0))
        (Matrix.single i j (1 : ℂ)) = -Matrix.single i j (1 : ℂ)) ∧
    (∀ phi : ℝ, adjointConjugation (jointZ n phi) (Matrix.single i j (1 : ℂ)) = -Matrix.single i j (1 : ℂ) →
      QAlgorithms.hammingWeight i ≠ QAlgorithms.hammingWeight j) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
