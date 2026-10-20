-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_support_failure_tests
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.support_failure_tests
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:56:14.287395+00:00
-- url     : https://prove2.me/theorems/2be7675b-a28e-4fe3-8511-ac5f773d0577
-- title:
--   Support failure admits exponentially successful zero-beta tests
-- statement:
--   Let ρ and σ be density operators with supp ρ not contained in supp σ. Put c=Tr(ρ σ⁰), where σ⁰ is its support projector, and Tₙ=I−(σ^{⊗n})⁰. For every n≥1 these are valid tests accepting ρ, and
--
--   $$
--   \beta_n(T_n)=0\leq e^{-nr}\ (r>0),\qquad\alpha_n(T_n)=c^n,\qquad\lim_n\frac1n\log\alpha_n(T_n)=\log c,\qquad-\log c>0.
--   $$
--
--   These tests explain why support inclusion is needed in the subsequent strong-converse analysis.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 10, Remark IV.1 Note that if supp ρ ⊆ supp σ is not satisfied then the strong converse property doesn’t

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.10: Support failure admits exponentially successful zero-beta tests. Extended log includes c=0, giving alpha_n=0 and exponent +infinity. No unequal-state or support-inclusion premise from later subsections is imported. -/
theorem support_failure_tests (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : ¬ SupportLE rho sigma) :
    (∀ n : ℕ, 1 ≤ n →
      let T : Mat (Fin n → I) := 1 - support (copies n sigma)
      IsEffect T ∧ accept sigma n T = 0 ∧
      (∀ r : ℝ, 0 < r → accept sigma n T ≤ Real.exp (-(n : ℝ) * r)) ∧
      typeI rho n T = (tr (rho * support sigma)) ^ n) ∧
    0 < -logNonnegativeExtended (tr (rho * support sigma)) ∧
    Tendsto (fun n => scaled n (logNonnegativeExtended (typeI rho (n + 1) (1 - support (copies (n + 1) sigma)))))
      atTop (nhds (logNonnegativeExtended (tr (rho * support sigma)))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
