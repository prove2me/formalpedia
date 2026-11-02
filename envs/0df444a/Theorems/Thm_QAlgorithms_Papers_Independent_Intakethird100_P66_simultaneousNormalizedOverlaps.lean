-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P66_simultaneousNormalizedOverlaps
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P66.simultaneousNormalizedOverlaps
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:45:34.081687+00:00
-- url     : https://prove2.me/theorems/e6c5f2d9-fe96-4016-8f5f-6d2ab5c22015
-- title:
--   Simultaneous normalized process-overlap prediction
-- statement:
--   Fix $n\ge1$, $M\ge1$, trace-one positive semidefinite input/output matrices $(\rho_i^{\rm in},\sigma_i)_{i=1}^M$ before sampling, and $0<\epsilon,\delta<1$. Put $O_i=(\rho_i^{\rm in})^T\otimes\sigma_i$, $O_i^0=O_i-\operatorname{Tr}(O_i)I/4^n$, and $L=\epsilon^{-2}\log(2M/\delta)$. For any unknown CPTP channel, write $\rho_{\Lambda}=2^{-n}\Lambda_{\mathcal E}$.
--
--   An absolute $C>0$, independent of system size, family, primitive, accuracy, confidence and channel, gives the following sufficient total counts. For an arbitrary fixed informationally complete primitive $\mathcal U$, use $\lceil CL\max_i\|O_i^0\|_{\mathrm{shadow},\mathcal U}^2\rceil$. For global Clifford measurements, use $\lceil CL\max_i\operatorname{Tr}(O_i^2)\rceil$. For independent single-qubit Cliffords, if $O_i$ is the identity outside a specified subset of $k_i$ of all $2n$ Choi wires, use $\lceil CL\max_i4^{k_i}\|O_i\|_\infty^2\rceil$. In each case an estimator chosen independently of the channel, on that many independent fresh-shot records, satisfies
--
--   $$
--   \Pr\!\left[\forall i,\ \left|\widehat o_i-\operatorname{Tr}(O_i\rho_{\Lambda})\right|\le\epsilon\right]\ge1-\delta.
--   $$
--
--   For each pure input/output pair,
--
--   $$
--   \operatorname{Tr}(O_i^2)=1,\qquad \|O_i\|_\infty^2=1.
--   $$
--
--   The shadow norm uses the inverse measurement channel and the worst normalized-state second moment. The physical overlap is $2^n$ times the normalized target, so physical accuracy $\epsilon$ requires normalized accuracy $\epsilon/2^n$ (or $\epsilon/2^k$ for a reduced process). The result permits one data set to predict many fixed normalized queries. For the general Borel measurement primitive, the estimator is measurable, so the simultaneous success event is measurable.
-- source:
--   Classical Shadows for Quantum Process Tomography on Near-term Quantum Computers, arXiv:2110.02965v3, PDF p. 2, Theorem II.2 (informal)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P66

noncomputable section

open MeasureTheory QAlgorithms ClassicalShadows

open scoped Matrix ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Intakethird100.P66

attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Theorem II.2 (informal), PDF pp.2-3; proof-defined observable in A.2 p.13.
Printed Tr(O)/2 becomes Tr(O)/4^n; both specialization logarithms retain delta.
The global factor 3 is absorbed only in this order bound. Pure-pair clauses
refer to normalized density matrices. -/
theorem simultaneousNormalizedOverlaps [∀ m : ℕ, Fintype (Clifford.ProjectiveGroup m)] :
    ∃ C : ℝ, 0 < C ∧ ∀ (n M : ℕ), 0 < n → 0 < M →
      ∀ (rho sigma : Fin M → Space n),
        (∀ i, IsDensityMatrix (rho i)) → (∀ i, IsDensityMatrix (sigma i)) →
      ∀ (eps delta : ℝ), 0 < eps → eps < 1 → 0 < delta → delta < 1 →
      let O : Fin M → Space (n + n) := fun i => overlapObservable (rho i) (sigma i)
      let L := Real.log (2 * (M : ℝ) / delta) / eps ^ 2
      (∀ P : MeasurementPrimitive (n + n),
        PrimitiveOverlapsRecover P O
          ⌈C * L * finiteMax (fun i => centeredVariance P (O i))⌉₊ eps delta) ∧
      OverlapsRecover (globalFrame (n + n)) O
        ⌈C * L * finiteMax (fun i => ((O i) ^ 2).trace.re)⌉₊ eps delta ∧
      (∀ s : Fin M → Finset (Fin (n + n)), (∀ i, ActsWithin (s i) (O i)) →
        OverlapsRecover (singleCliffordFrame (n + n)) O
          ⌈C * L * finiteMax (fun i => (4 : ℝ) ^ (s i).card * specNorm (O i) ^ 2)⌉₊
          eps delta) ∧
      (∀ i, (∃ psi : EuclideanSpace ℂ (Qubits n), IsState psi ∧ rho i = pureDensity psi) →
        (∃ psi : EuclideanSpace ℂ (Qubits n), IsState psi ∧ sigma i = pureDensity psi) →
        ((O i) ^ 2).trace.re = 1 ∧ specNorm (O i) ^ 2 = 1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P66

end
