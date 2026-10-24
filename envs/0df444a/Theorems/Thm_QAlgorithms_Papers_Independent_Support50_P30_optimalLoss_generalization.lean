-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P30_optimalLoss_generalization
-- name    : QAlgorithms.Papers.Independent.Support50.P30.optimalLoss_generalization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:24:51.478757+00:00
-- url     : https://prove2.me/theorems/f8f399dc-12f2-41b0-9788-772952f5f17b
-- title:
--   Unnumbered closeness of optimal empirical and population losses
-- statement:
--   Use the bounded measurable loss and i.i.d. sampling assumptions of Theorem 4 with $\|O\|_{\mathrm{op}}\le1$. Fix the same nonempty class $\mathcal V$ of commuting unitaries for both risks, and define $\widehat L^*=\inf_{U\in\mathcal V}\widehat L_S(U)$ and $L^*=\inf_{U\in\mathcal V}L(U)$. There is a universal $C>0$ such that for $n\ge2$, $0<\epsilon,\delta<1$ and a positive integer sample budget with $M\ge C(\binom{n+3}{3}+\log(1/\delta))/\epsilon^2$,
--
--   $$\Pr\!\left(|\widehat L^*-L^*|\le\epsilon\right)\ge1-\delta.$$
--
--   Both risk sets are nonempty and bounded by the weight and observable bounds. This compares infima and does not require that an optimizer exists.
-- source:
--   Theoretical Guarantees for Permutation-Equivariant Quantum Neural Networks, arXiv:2210.09974v3, PDF p. 7, Unnumbered closeness of optimal empirical and population losses

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P30

/-- PDF p.7: infima over the same nonempty class. The explicit weight and
observable bounds keep both sets of risk values bounded. -/
theorem optimalLoss_generalization :
    ∃ C : ℝ, 0 < C ∧ ∀ (n M : ℕ), 2 ≤ n → 1 ≤ M →
    ∀ (epsilon deltaConf : ℝ), 0 < epsilon → epsilon < 1 →
      0 < deltaConf → deltaConf < 1 →
      C * (((n + 3).choose 3 : ℝ) + Real.log (1 / deltaConf)) / epsilon ^ 2 ≤ (M : ℝ) →
    ∀ (P : Measure (QnnDensity n)), IsProbabilityMeasure P →
    ∀ (a : QnnDensity n → ℝ), Measurable a → (∀ rho, |a rho| ≤ 1) →
    ∀ (O : QnnOperator n), O.IsHermitian → PermutationEquivariant O → specNorm O ≤ 1 →
    ∀ V : Set (QnnOperator n), V.Nonempty → V ⊆ unitaryFamily n →
      (Measure.pi (fun _ : Fin M => P))
        {xs | |sInf (Set.range (fun U : V => empiricalRisk a O U.val xs)) -
          sInf (Set.range (fun U : V => qnnPopulationRisk P a O U.val))| ≤ epsilon} ≥
        ENNReal.ofReal (1 - deltaConf) := by sorry

end QAlgorithms.Papers.Independent.Support50.P30

end
