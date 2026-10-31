-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P76_separability_iff_restricted_trace_one
-- name    : QAlgorithms.Papers.Independent.Intake100.P76.separability_iff_restricted_trace_one
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:22:11.457273+00:00
-- url     : https://prove2.me/theorems/1a3452ec-7ef9-4d61-b54f-58ff5390eb45
-- title:
--   Separability iff an attained restricted BSA has trace one
-- statement:
--   Let $H_A$ and $H_B$ be finite-dimensional nonzero complex Hilbert spaces, with $H_A$ the first tensor factor, and let $\rho$ be a positive semidefinite operator of trace one on $H_A\otimes H_B$. For a set $V$ of unit product vectors in $\operatorname{range}\rho$, write $C(V)$ for all finite nonnegative sums of projectors onto vectors in $V$, including zero. Then
--
--   $$\rho\text{ is separable}\iff\exists V\subseteq\operatorname{range}\rho,\ \exists S\in C(V):\ \rho-S\succeq0,\ \operatorname{Tr}S=1,\ \forall T\in C(V),\ \rho-T\succeq0\Rightarrow\operatorname{Tr}T\leq\operatorname{Tr}S.$$
--
--   The set and its attained optimizer are existential witnesses. No attainment assertion for an arbitrary prescribed set is required.
-- source:
--   Separability and entanglement of composite quantum systems, arXiv:quant-ph/9707043v1, PDF p. 2, Condition 3: separability iff a restricted BSA has trace one

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P76

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

open QAlgorithms QAlgorithms.Entanglement

namespace QAlgorithms.Papers.Independent.Intake100.P76

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

/-- PDF p.2, Condition 3: an existential prescribed-set BSA of trace one
characterizes separability, without assuming attainment for arbitrary V. -/
theorem separability_iff_restricted_trace_one [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    IsSeparableDensity rho ↔
      ∃ V : Set (EuclideanSpace ℂ (A × B)),
        (∀ v ∈ V, IsUnitProduct v ∧ v ∈ LinearMap.range (Matrix.toEuclideanLin rho)) ∧
        ∃ S, IsBSAOver rho V S ∧ S.trace.re = 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P76

end
