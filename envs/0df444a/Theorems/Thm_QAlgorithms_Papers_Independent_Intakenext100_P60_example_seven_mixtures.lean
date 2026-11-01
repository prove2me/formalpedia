-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P60_example_seven_mixtures
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P60.example_seven_mixtures
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:58:43.068983+00:00
-- url     : https://prove2.me/theorems/da192256-fed8-4827-bff6-212c18ab6e45
-- title:
--   Example 7: direct-sum family with constant formation and cost in [3/2,log 3]
-- statement:
--   In $\mathbb C^3\otimes\mathbb C^6$ let $K$ be the span of the three unit vectors
--   $$|j\rangle_s=\tfrac12\bigl(|j+1\bmod3\rangle|j+2\bmod3\rangle+|j+2\bmod3\rangle|j+1\bmod3\rangle+\sqrt2\,|j\rangle|j+3\rangle\bigr),\quad j=0,1,2.$$
--   The last environment indices are the ordinary integers $3,4,5$.
--
--   Let $|\Phi_3\rangle=3^{-1/2}\sum_{r=0}^2|r\rangle|r\rangle$ and $|j\rangle_t=|\Phi_3\rangle\otimes|j\rangle$. Choose complex $c,s$ with $|c|^2+|s|^2=1$, and let $K_{c,s}$ be the span of the coherent direct-sum vectors $c|j\rangle_s\oplus s|j\rangle_t$ in $\mathbb C^3\otimes(\mathbb C^6\oplus\mathbb C^9)$. Put $t=|c|^2$, $a=(1-t)/3+t/2$, $b=(1-t)/3+t/4$, and $h(c)=-a\log_2a-2b\log_2b$. Every density matrix $\rho$ supported on $K_{c,s}$ satisfies
--   $$E_c(\rho)=E_f(\rho)=h(c),\qquad\tfrac32\le h(c)\le\log_2 3.$$
--   The endpoints correspond respectively to the original subspace and the maximally entangled constant-channel branch. The explicit constant is the entropy of the printed channel's spectrum $(a,b,b)$.
--
--   Here $E_f$ is the infimum of average pure-state marginal entropy over normalized finite decompositions of the stated density matrix. $E_c$ is the asymptotic EPR preparation rate under deterministic two-way LOCC, and $E_D$ is the corresponding asymptotic distillation rate, in bits per copy. All entropies and logarithms are in bits.
-- source:
--   Remarks on additivity of the Holevo channel capacity and of the entanglement of formation, arXiv:quant-ph/0206148v4, PDF p. 13, Example 7: direct-sum family with constant formation and cost in [3/2,log 3]

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

/-- PDF p.13, Example 7 continuation: the direct-sum family, including both pure
branches, has constant cost and formation with the printed closed interval of values. -/
theorem example_seven_mixtures (c s : ℂ) (hcs : Complex.normSq c + Complex.normSq s = 1)
    (rho : Op (Fin 3 × (Fin 6 ⊕ (Fin 3 × Fin 3)))) (hrho : IsDensityMatrix rho)
    (hsupport : HasRangeIn (dilationSpace (exampleSevenMixtureDilation c s)) rho) :
    formationCostBits rho = exampleSevenMixtureEntropy c ∧ formation rho = exampleSevenMixtureEntropy c ∧
      3 / 2 ≤ exampleSevenMixtureEntropy c ∧ exampleSevenMixtureEntropy c ≤ Real.logb 2 3 := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P60
