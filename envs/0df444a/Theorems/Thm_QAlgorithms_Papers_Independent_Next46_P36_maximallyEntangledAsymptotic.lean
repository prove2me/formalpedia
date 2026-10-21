-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P36_maximallyEntangledAsymptotic
-- name    : QAlgorithms.Papers.Independent.Next46.P36.maximallyEntangledAsymptotic
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:45:14.62599+00:00
-- url     : https://prove2.me/theorems/4548bb6b-b37b-4f97-8611-c7b05e7379e0
-- title:
--   Optimal supplied-state fidelity has leading infidelity 3/(4N)
-- statement:
--   For the same supplied $N$ identical two-qubit maximally entangled states, Haar prior, physical tensor action, arbitrary joint POVMs and single-copy squared-overlap loss as in the finite-copy theorem, let $R_{\rm opt}(N)$ be the genuine infimum of the average infidelity. Then
--
--   $$\lim_{N\to\infty}N R_{\rm opt}(N)=\frac34.$$
--
--   Equivalently, the optimal fidelity is $F_{\rm opt}(N)=1-3/(4N)+o(N^{-1})$. The limit is over all integers and includes both parities. It asserts a leading asymptotic rather than a finite-$N$ identity; the spin-zero correction is negligible at this scale.
-- source:
--   Optimal estimation of group transformations using entanglement, arXiv:quant-ph/0506267v2, PDF p. 9, §IV B, Eqs. (67)-(68)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P36

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Next46.P36

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P36.matrixMeasurable

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- PDF pp.1,9 Eqs.(67)-(68): a leading asymptotic, covering both parities.
Optimal single-copy fidelity is 1-optimalBellRisk; preparation is not optimized. -/
theorem maximallyEntangledAsymptotic
    [IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ)] [CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ)] [MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ)] [BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (dg : Measure (Matrix.specialUnitaryGroup (Fin 2) ℂ)) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg] :
    Tendsto (fun N : ℕ => (N : ℝ) * optimalBellRisk dg N) atTop (nhds (3 / 4 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P36

end
