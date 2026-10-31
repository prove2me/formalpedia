-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P90_measurementBasis_reduction
-- name    : QAlgorithms.Papers.Independent.Intake100.P90.measurementBasis_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:09:38.002151+00:00
-- url     : https://prove2.me/theorems/6d91c9b3-10d2-42d1-b2d5-9c177044e044
-- title:
--   Diagonal unitary mixtures preserve complete measurement blocks
-- statement:
--   Let $\rho$ be a normalized density matrix on finite registers $A\otimes B$, with their known orthonormal measurement bases. Let $p_j\ge0$ with $\sum_jp_j=1$, and let $O_j$ be unitaries diagonal in Alice's measurement basis. Define $\rho'_A=\sum_j p_j(O_j\otimes I)\rho(O_j^\dagger\otimes I)$. For each Alice basis label $x$, writing $P_x=|x\rangle\langle x|$, one has
--
--   $$(P_x\otimes I)\rho'_A(P_x\otimes I)=(P_x\otimes I)\rho(P_x\otimes I).$$
--
--   The analogous assertion holds for any normalized mixture of Bob's basis-diagonal unitaries, with projectors $I\otimes P_y$. The identity preserves both outcome probabilities and the remaining systems' unnormalized conditional states, and justifies the measurement-equivalent diagonal randomization used in the protocol reduction.
-- source:
--   Lower and upper bounds on the secret key rate for QKD protocols using one--way classical communication, arXiv:quant-ph/0410215v2, PDF p. 2, Unnumbered measurement-basis reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P90

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P90

/-- PDF p.2: equality of the entire projected blocks, on either subsystem,
under a normalized mixture of diagonal unitaries in the known basis. -/
theorem measurementBasis_reduction {I J K : Type*}
    [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J]
    (rho : Matrix (I × J) (I × J) ℂ) (hrho : IsDensityMatrix rho)
    (p : K → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : ∑ k, p k = 1)
    (OA : K → Matrix.unitaryGroup I ℂ) (OB : K → Matrix.unitaryGroup J ℂ)
    (hA : ∀ k, ∃ d : I → ℂ, (∀ x, Complex.normSq (d x) = 1) ∧
      (OA k : Matrix I I ℂ) = Matrix.diagonal d)
    (hBB : ∀ k, ∃ d : J → ℂ, (∀ x, Complex.normSq (d x) = 1) ∧
      (OB k : Matrix J J ℂ) = Matrix.diagonal d) :
    (∀ x : I, let P := Matrix.kronecker (pureDensity (ket x)) (1 : Matrix J J ℂ)
      P * mixOnFirst p (fun k => (OA k : Matrix I I ℂ)) rho * P = P * rho * P) ∧
    (∀ y : J, let P := Matrix.kronecker (1 : Matrix I I ℂ) (pureDensity (ket y))
      P * mixOnSecond p (fun k => (OB k : Matrix J J ℂ)) rho * P = P * rho * P) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P90

end
