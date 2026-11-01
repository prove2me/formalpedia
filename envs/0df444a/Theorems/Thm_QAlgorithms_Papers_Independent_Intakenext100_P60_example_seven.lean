-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P60_example_seven
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P60.example_seven
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:57:49.552877+00:00
-- url     : https://prove2.me/theorems/679ed312-1b2a-4359-ad15-c5f8d11b01be
-- title:
--   Example 7: the displayed C3⊗C6 subspace has formation and cost 3/2
-- statement:
--   In $\mathbb C^3\otimes\mathbb C^6$ let $K$ be the span of the three unit vectors
--   $$|j\rangle_s=\tfrac12\bigl(|j+1\bmod3\rangle|j+2\bmod3\rangle+|j+2\bmod3\rangle|j+1\bmod3\rangle+\sqrt2\,|j\rangle|j+3\rangle\bigr),\quad j=0,1,2.$$
--   The last environment indices are the ordinary integers $3,4,5$.
--
--   Every density matrix $\rho$ supported on $K$ obeys
--   $$E_c(\rho)=E_f(\rho)=\tfrac32.$$
--   This worked deduction uses the Vidal--Dür--Cirac subspace [33] and Shor's entanglement-breaking channel additivity theorem [29].
--
--   Here $E_f$ is the infimum of average pure-state marginal entropy over normalized finite decompositions of the stated density matrix. $E_c$ is the asymptotic EPR preparation rate under deterministic two-way LOCC, and $E_D$ is the corresponding asymptotic distillation rate, in bits per copy. All entropies and logarithms are in bits.
-- source:
--   Remarks on additivity of the Holevo channel capacity and of the entanglement of formation, arXiv:quant-ph/0206148v4, PDF p. 13, Example 7: the displayed C3⊗C6 subspace has formation and cost 3/2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P60

namespace QAlgorithms.Papers.Independent.Intakenext100.P60

open scoped Matrix ComplexConjugate ComplexOrder TensorProduct

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix, normalized ensemble, convex roof, grouped copies and LOCC.

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble pureAverage formation)

open QAlgorithms.Papers.Independent.Information100.P80 (groupedPower)

open QAlgorithms.Papers.Independent.Gap48.P32 (twoWayDistillable)

/-- PDF pp.12--13, Example 7: every supported state has cost=formation=3/2 bits.
The subspace is credited to Vidal--Dur--Cirac [33], the capacity input to Shor [29]. -/
theorem example_seven (rho : Op (Fin 3 × Fin 6)) (hrho : IsDensityMatrix rho)
    (hsupport : HasRangeIn (dilationSpace exampleSevenDilation) rho) :
    formationCostBits rho = 3 / 2 ∧ formation rho = 3 / 2 := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P60
