-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P30_generalization_bound
-- name    : QAlgorithms.Papers.Independent.Support50.P30.generalization_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:23:27.869951+00:00
-- url     : https://prove2.me/theorems/60801088-a053-4c0e-8099-6aed902c149d
-- title:
--   Theorem 4 (Generalization bound)
-- statement:
--   Fix the observable normalization $\|O\|_{\mathrm{op}}\le1$. There is a universal $C>0$ such that the following holds for $n\ge2$, $M\ge1$, and $0<\delta<1$. Let $P$ be a Borel probability measure on $n$-qubit density matrices, let $a(\rho)$ be a measurable label-dependent coefficient with $|a(\rho)|\le1$, and let $O$ be a Hermitian permutation-equivariant observable. Define $L(U)=\mathbb E_{\rho\sim P}[a(\rho)\operatorname{Tr}(U\rho U^\dagger O)]$ and $\widehat L_S(U)=M^{-1}\sum_i a(\rho_i)\operatorname{Tr}(U\rho_iU^\dagger O)$ for $M$ independent samples from $P$. With probability at least $1-\delta$, simultaneously for all commuting unitaries $U$,
--
--   $$|L(U)-\widehat L_S(U)|\le C\left(\sqrt{\frac{\binom{n+3}{3}}M}+\sqrt{\frac{\log(1/\delta)}M}\right).$$
--
--   The logarithm is natural. The coefficient $a$ denotes the composition of the label weight with the labeling function; the population coefficient is not divided by $M$. The uniform event applies in particular to any trained parameters selected from the data.
-- source:
--   Theoretical Guarantees for Permutation-Equivariant Quantum Neural Networks, arXiv:2210.09974v3, PDF p. 7, Theorem 4 (Generalization bound)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P30

/-- PDF p.7, Theorem 4, Eq.(20); p.15 fixes bounded measurable losses.
Fix K=1; C is universal and the event is uniform in the trained parameters. -/
theorem generalization_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n M : ℕ), 2 ≤ n → 1 ≤ M →
    ∀ (P : Measure (QnnDensity n)), IsProbabilityMeasure P →
    ∀ (a : QnnDensity n → ℝ), Measurable a → (∀ rho, |a rho| ≤ 1) →
    ∀ (O : QnnOperator n), O.IsHermitian → PermutationEquivariant O → specNorm O ≤ 1 →
    ∀ deltaConf : ℝ, 0 < deltaConf → deltaConf < 1 →
      (Measure.pi (fun _ : Fin M => P))
        (generalizationEvent P a O
          (C * (Real.sqrt (((n + 3).choose 3 : ℝ) / (M : ℝ)) +
            Real.sqrt (Real.log (1 / deltaConf) / (M : ℝ))))) ≥
        ENNReal.ofReal (1 - deltaConf) := by sorry

end QAlgorithms.Papers.Independent.Support50.P30

end
