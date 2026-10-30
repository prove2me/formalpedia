-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P12_entropy_SDP_duality
-- name    : QAlgorithms.Papers.Independent.Advance50.P12.entropy_SDP_duality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:15:41.887287+00:00
-- url     : https://prove2.me/theorems/8299efb2-fdcf-400c-9255-625265c14b9c
-- title:
--   Lemma 4: entropy SDP duality, including the classical restriction
-- statement:
--   Let $H_A,H_B$ be positive-dimensional finite-dimensional complex Hilbert spaces in chosen orthonormal bases. For every positive semidefinite operator $\rho_{AB}$, including the zero operator,
--   $$\min_{\sigma_B\ge0,\ I_A\otimes\sigma_B\ge\rho_{AB}}\operatorname{tr}\sigma_B=\max_{E_{AB}\ge0,\ \operatorname{tr}_AE_{AB}=I_B}\operatorname{tr}(\rho_{AB}E_{AB}).$$
--   Both extrema are attained; the minimizing $\sigma_B$ is not required to have trace one. If $\rho_{AB}$ is classical on $A$ in the chosen basis, a maximizing $E_{AB}$ can be chosen classical in that same basis. Classicality means Hermitian with all off-diagonal $A$ blocks zero. The Lean statement gives feasible optimizers, their equal values, both optimality comparisons, and a classical optimizer when appropriate. This is the entropy semidefinite-programming duality used by the operational identities.
-- source:
--   The operational meaning of min- and max-entropy, arXiv:0807.1338v2, PDF p. 8, Lemma 4 / (29)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P12

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData cqDensity)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative elog marginalAB)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Renew46.P35 (traceAdjoint)

open QAlgorithms.Papers.Independent.Support50.P23 (exp2Extended independentProduct)

variable {A B C D X : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype X]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq X]

/-- PDF p.8, Lemma 4 / (29): equal attained primal and dual optima,
including an attained classical dual optimum in the same basis whenever rho is
classical. The PSD input may be zero and need not be normalized. -/
theorem entropy_SDP_duality [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : rho.PosSemidef) :
    ∃ sigma : Matrix B B ℂ, ∃ e : Matrix (A × B) (A × B) ℂ,
      EntropyPrimalFeasible rho sigma ∧ EntropyDualFeasible e ∧
      sigma.trace.re = (rho * e).trace.re ∧
      (∀ sigma2, EntropyPrimalFeasible rho sigma2 → sigma.trace.re ≤ sigma2.trace.re) ∧
      (∀ e2, EntropyDualFeasible e2 → (rho * e2).trace.re ≤ (rho * e).trace.re) ∧
      (ClassicalOnFirst rho → ∃ ec : Matrix (A × B) (A × B) ℂ,
        EntropyDualFeasible ec ∧ ClassicalOnFirst ec ∧ (rho * ec).trace.re = sigma.trace.re) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P12

end
