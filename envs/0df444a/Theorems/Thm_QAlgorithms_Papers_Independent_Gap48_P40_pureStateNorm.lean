-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_pureStateNorm
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.pureStateNorm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:19:55.534986+00:00
-- url     : https://prove2.me/theorems/80858ae6-434d-4ed4-b820-ba082424108b
-- title:
--   §IV, unnumbered pure-state distance formula
-- statement:
--   Let $N$ be any genuine unitarily invariant norm on $d\times d$ complex matrices. Write $E=\operatorname{diag}(1,0,\ldots)$ and, when $d\ge2$, $F=\operatorname{diag}(1,-1,0,\ldots)$. The symbols $\|\cdot\|_\infty$, $\|\cdot\|_1$ and $\|\cdot\|_2$ mean operator, full trace and Hilbert–Schmidt norms, respectively. Let $d\ge2$ and let $\psi,\phi$ be unit vectors. Then
--
--   $$
--   N(|\psi\rangle\langle\psi|-|\phi\rangle\langle\phi|)=\sqrt{1-|\langle\psi,\phi\rangle|^2}\,N(F).
--   $$
--
--   Equality with $N(F)$ holds exactly when the vectors are orthogonal. Every pair of mixed states also has distance at most $N(F)$.
--
--   Orthogonal pure states therefore give the maximal state distance for every UI norm.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 3, §IV, unnumbered pure-state distance formula

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

/-- PDF p.3: pure-state formula, orthogonality equality, and global maximality. -/
theorem pureStateNorm {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ) (hN : IsUINorm N)
    (psi phi : EuclideanSpace ℂ (Fin d)) (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1) :
    N (pureDensity psi - pureDensity phi) =
      Real.sqrt (1 - ‖inner ℂ psi phi‖ ^ 2) * N (matrixF d) ∧
    (N (pureDensity psi - pureDensity phi) = N (matrixF d) ↔ inner ℂ psi phi = 0) ∧
    (∀ rho sigma : Mat d, IsDensityMatrix rho → IsDensityMatrix sigma →
      N (rho - sigma) ≤ N (matrixF d)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
