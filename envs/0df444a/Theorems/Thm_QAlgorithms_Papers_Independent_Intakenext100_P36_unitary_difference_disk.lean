-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P36_unitary_difference_disk
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P36.unitary_difference_disk
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:15:42.813153+00:00
-- url     : https://prove2.me/theorems/c8ea5849-dfd5-44b2-8490-922cb7138978
-- title:
--   Theorem 26: unitary differences and the smallest spectral disk
-- statement:
--   Let $n\ge1$, let $U\in M_n$ be unitary, and define the complex-linear map $\Phi(X)=UXU^\dagger-X$ on all matrices. There exist $c\in\mathbb C$ and $r\ge0$ such that the closed disk $\{z:|z-c|\le r\}$ contains the spectrum of $U$ and $r$ is no greater than the radius of any other closed disk containing that spectrum. For this smallest radius,
--
--   $$\|\Phi\|_{\rm cb}=\|\Phi^\dagger\|_{\rm cb}=\|\Phi\|_\diamond=\|\Phi^\dagger\|_\diamond=2r.$$
--
--   The dual is the bilinear trace dual; the diamond norm uses unnormalized trace norm without a factor $1/2$. Scalar unitaries are included, with $r=0$.
--
--   This geometric formula computes the common stabilized norm from a smallest enclosing disk, whose diameter need not equal the maximum distance between two eigenvalues. The paper gives a new elementary proof of a previously known formula.
-- source:
--   Computing Stabilized Norms for Quantum Operations via the Theory of Completely Bounded Maps, arXiv:0711.3636v1, PDF p. 13, Theorem 26

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P36

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P36

local notation "Mat" => QAlgorithms.Papers.Independent.Information100.P50.M

local notation "Map" => QAlgorithms.Papers.Independent.Information100.P50.Lin

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

/-- Theorem 26, PDF pp.13–14: four norms equal twice the least enclosing radius.
This paper supplies an elementary proof of an earlier geometric formula. -/
theorem unitary_difference_disk {n : ℕ} (hn : 0 < n)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ center : ℂ, ∃ radius : ℝ,
      IsSmallestSpectralDisk (U : Mat n) center radius ∧
      extendedCBNorm (unitaryDifference (U : Mat n)) = ENNReal.ofReal (2 * radius) ∧
      extendedCBNorm (traceDual (unitaryDifference (U : Mat n))) = ENNReal.ofReal (2 * radius) ∧
      rectangularDiamondNorm (unitaryDifference (U : Mat n)) = ENNReal.ofReal (2 * radius) ∧
      rectangularDiamondNorm (traceDual (unitaryDifference (U : Mat n))) =
        ENNReal.ofReal (2 * radius) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P36

end
