-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P99_loss_amplifies_coin_disturbance
-- name    : QAlgorithms.Papers.Independent.Intake100.P99.loss_amplifies_coin_disturbance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:14:28.354084+00:00
-- url     : https://prove2.me/theorems/d8cc46c4-e1f2-4857-b3e4-f0052df84586
-- title:
--   Loss amplification of the disturbed-coin fraction
-- statement:
--   Consider a family of normalized joint states of $n$ original virtual coins and the classical removal flags, with arbitrary correlations. Let $0\leq\Delta\leq1$ and $0\leq f<1$. Every removal mask with nonzero probability removes at most $nf$ signals. Let $N_X$ be the number of original $X$-minus coins, $L$ the number of removed signals, and $N_{X,\mathrm{ret}}$ the number of minus coins at the surviving positions. If $\Pr[N_X\geq n\Delta]$ is exponentially small, then
--
--   $$
--   \Pr\!\left[\frac{N_{X,\mathrm{ret}}}{n-L}\geq\frac\Delta{1-f}\right]\leq e^{-Cn}\qquad(n\geq n_0)
--   $$
--
--   for some $C>0$ and $n_0$. Thus the surviving disturbed fraction is bounded by the original disturbed fraction divided by the retained fraction. The exact-fraction case $L=nf$ is included; an upper bound on the loss fraction gives the same conservative estimate. The fraction on the left is computed from the actual outcomes and mask, rather than supplied as an unrelated parameter.
--
--   **Formalization Note** All virtual coins are retained in the joint experiment used to count outcomes, including those belonging to lost signals; the loss flags commute with their hypothetical $X$ measurement. This is the counting normalization in equation (32), with no conditioning on rare block acceptance.
-- source:
--   Security of quantum key distribution with imperfect devices, arXiv:quant-ph/0212066v3, PDF p. 12, Unnumbered loss amplification of coin disturbance, eq.(32)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P99

noncomputable section

open scoped Matrix ComplexConjugate BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P99

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Dependency50.P48 (IsDilation receiver)

/-- arXiv:quant-ph/0212066v3, PDF p.12, (32).
Retained disturbance is computed using the actual loss mask and original-to-
retained normalization. The budget is an upper bound, so exact loss fractions
are included. The joint Born law includes arbitrarily correlated removal masks. -/
theorem loss_amplifies_coin_disturbance
    (delta loss : ℝ) (hdelta : 0 ≤ delta ∧ delta ≤ 1)
    (hloss : 0 ≤ loss ∧ loss < 1)
    (rho : (n : ℕ) → Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ)
    (hstate : ∀ n, IsDensityMatrix (rho n))
    (hmask : ∀ n, LossBudget (rho n) loss)
    (hbalanced : ExponentiallySmall
      (fun n => coinXFailure (traceRight (rho n)) delta)) :
    ExponentiallySmall (fun n => retainedLossFailure (rho n) delta loss) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P99

end
