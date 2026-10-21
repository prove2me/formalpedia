-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P43_ssaEqualityIffSufficiency
-- name    : QAlgorithms.Papers.Independent.Next46.P43.ssaEqualityIffSufficiency
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:45:33.413027+00:00
-- url     : https://prove2.me/theorems/e0a32938-0f7c-4c45-b4a0-5779d5926551
-- title:
--   Unnumbered: SSA equality is relative-entropy equality and sufficiency
-- statement:
--   Let $\rho_{ABC}$ be a normal state on separable complex $H_A\otimes H_B\otimes H_C$, and assume $S(\rho_{ABC}),S(\rho_B),S(\rho_{AB}),S(\rho_{BC})$ are finite. Let $\rho_A$ be the $A$ marginal and put $\sigma_{ABC}=\rho_A\otimes\rho_{BC}$. Then the following three conditions are equivalent:
--
--   $$
--   \begin{aligned}
--   &S(\rho_{ABC})+S(\rho_B)=S(\rho_{AB})+S(\rho_{BC});\\
--   &D(\rho_{AB}\|\rho_A\otimes\rho_B)=D(\rho_{ABC}\|\sigma_{ABC});\\
--   &B(H_A\otimes H_B)\otimes\mathbb C I_C
--   \text{ is sufficient for }\{\rho_{ABC},\sigma_{ABC}\}.
--   \end{aligned}
--   $$
--
--   Here $D$ is extended Umegaki relative entropy in nats. Sufficiency means one normal-predual trace-preserving 2-positive reverse map recovers both states from their $AB$ restrictions. It is defined independently of entropy equality. Nonfaithful states are allowed via the source support reduction. This connects the entropy equality to statistical sufficiency.
-- source:
--   Sufficiency in quantum statistical inference, arXiv:math-ph/0412093v1, PDF p. 24, Unnumbered: SSA equality is relative-entropy equality and sufficiency

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P43

noncomputable section

open MeasureTheory Filter

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P43

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (homogeneousEntropy generalizedRelativeEntropy traceFirst traceSecond)

/-- Unnumbered SSA equality interpretation, PDF p.24, (27)–(28).
All four entropies in (27) are finite, as required by the section preamble.
The second state is the computed product of the A and BC marginals.
Sufficiency is defined through one normal 2-positive recovery map for this
pair, and is not defined to mean entropy equality. Nonfaithful states are
allowed here; support compression is the source's p.11 reduction. -/
theorem ssaEqualityIffSufficiency
    {I J K : Type} [Countable I] [Countable J] [Countable K]
    (rho : State (I × (J × K)))
    (hABC : homogeneousEntropy rho.coefficients < ⊤)
    (hB : homogeneousEntropy (traceSecond (traceFirst rho.coefficients)) < ⊤)
    (hAB : homogeneousEntropy (MarginalAB rho.coefficients) < ⊤)
    (hBC : homogeneousEntropy (traceFirst rho.coefficients) < ⊤) :
    ((homogeneousEntropy rho.coefficients +
        homogeneousEntropy (traceSecond (traceFirst rho.coefficients)) =
      homogeneousEntropy (MarginalAB rho.coefficients) +
        homogeneousEntropy (traceFirst rho.coefficients)) ↔
      generalizedRelativeEntropy (MarginalAB rho.coefficients)
        (productCoeff (traceSecond (MarginalAB rho.coefficients))
          (traceSecond (traceFirst rho.coefficients))) =
      generalizedRelativeEntropy rho.coefficients (SsaFamily rho.coefficients false)) ∧
    ((homogeneousEntropy rho.coefficients +
        homogeneousEntropy (traceSecond (traceFirst rho.coefficients)) =
      homogeneousEntropy (MarginalAB rho.coefficients) +
        homogeneousEntropy (traceFirst rho.coefficients)) ↔
      SufficientTraceClassMap MarginalAB (SsaFamily rho.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P43

end
