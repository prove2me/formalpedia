-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P81_informational_distance_prediction_and_average
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P81.informational_distance_prediction_and_average
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:59:24.74478+00:00
-- url     : https://prove2.me/theorems/e75d3c2b-0d60-45eb-a9c0-be00a21b3e5f
-- title:
--   Prediction of a fair bit and the conditional-state average
-- statement:
--   Both statements use the full trace norm and $D(A:B)=\|\rho_{AB}-\rho_A\otimes\rho_B\|_1$.
--
--   1. Let $\rho_{AB}$ be a normalized bipartite state with $\rho_B=I_2/2$. Measure any Boolean POVM on $A$, obtaining $X$, and measure $B$ in its standard basis. For $0\le\varepsilon\le1$, suppose $\Pr(X=B)\ge1-\varepsilon$ and $\Pr(X\ne B)\le\varepsilon$. Applying the same measurement to the product of the marginals gives agreement and disagreement probabilities both equal to $1/2$, and
--   $$
--   D(A:B)\ge1-2\varepsilon.
--   $$
--   Only the bit marginal is required to be classical; the joint state can have quantum coherences.
--
--   2. Let $\rho_{AB}$ be normalized and block diagonal in the standard basis of $A$. Write $p_A(a)$ for the probability of $a$ and $\rho_B^{(a)}$ for the normalized conditional state whenever $p_A(a)>0$. Then
--   $$
--   D(A:B)=\sum_a p_A(a)\,\|\rho_B^{(a)}-\rho_B\|_1.
--   $$
--
--   These formulas connect prediction and classical conditioning to informational distance. Zero-probability outcomes contribute zero; their conditional matrix is assigned zero in the formalization.
-- source:
--   On rounds in quantum communication, arXiv:quant-ph/0004100v5, PDF p. 11, Lemma 3 (continued on PDF p.12)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P81

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intakethird100.P81

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Bridge50.P44 (ClassicalFirst)

/-- Lemma 3, PDF pp.11–12: fair-bit prediction AND the exact classical-quantum average.
Only the bit marginal is classical in clause 1; the joint state need not be classical. -/
theorem informational_distance_prediction_and_average :
    (∀ (A : Type) [Fintype A] [DecidableEq A]
      (rho : Matrix (A × Bool) (A × Bool) ℂ), IsDensityMatrix rho →
      traceLeft rho = (1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ) →
      ∀ (eps : ℝ), 0 ≤ eps → eps ≤ 1 →
      ∀ M : Bool → Matrix A A ℂ, IsPOVM M →
        agreement M rho ≥ 1 - eps → 1 - agreement M rho ≤ eps →
        agreement M (jointMarginalProduct rho) = 1 / 2 ∧
        1 - agreement M (jointMarginalProduct rho) = 1 / 2 ∧
        informationalDistance rho ≥ 1 - 2 * eps) ∧
    (∀ (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
      (rho : Matrix (A × B) (A × B) ℂ), IsDensityMatrix rho → ClassicalFirst rho →
        informationalDistance rho = ∑ a, classicalWeight rho a *
          traceNorm (firstRegisterConditionalBlock rho a - traceLeft rho)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P81

end
