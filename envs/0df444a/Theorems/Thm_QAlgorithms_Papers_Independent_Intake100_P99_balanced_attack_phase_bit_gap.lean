-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P99_balanced_attack_phase_bit_gap
-- name    : QAlgorithms.Papers.Independent.Intake100.P99.balanced_attack_phase_bit_gap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:12:46.917048+00:00
-- url     : https://prove2.me/theorems/0a21f809-524f-490d-ab92-b487e7f305af
-- title:
--   Phase and bit error gap for a balanced attack
-- statement:
--   Let $0\leq\Delta\leq\tfrac12$ and let $\rho_n$ be a normalized joint state of $n$ Alice--Bob qubit pairs and $n$ virtual basis coins after the complete attack and before the final coin-controlled bilateral Hadamards. Suppose that measuring the coins at this point in the $X$ basis gives $N_X<n\Delta$ except with exponentially small probability. After the controlled Hadamards, let $\widetilde\delta$ and $\widetilde\delta_p$ be the bit and phase error fractions in a joint Bell measurement of the pairs. With the nonnegative entropy-gap branch $f$ defined by $H_2(\tfrac12-f(\Delta))+H_2(\Delta)=1$, for every $\varepsilon>0$,
--
--   $$
--   \Pr\!\left[|\widetilde\delta_p-\widetilde\delta|\geq2(f(\Delta)+\varepsilon)\right]\leq e^{-Cn}\qquad(n\geq n_0)
--   $$
--
--   for some $C>0$ and $n_0$. The claim allows arbitrary correlations across pairs and coins. It is the concentration estimate that connects weak basis dependence to phase error inference; it is not a statement about mean error rates.
-- source:
--   Security of quantum key distribution with imperfect devices, arXiv:quant-ph/0212066v3, PDF p. 11, Lemma 2: phase/bit error gap for a balanced attack

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P99

noncomputable section

open scoped Matrix ComplexConjugate BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P99

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Dependency50.P48 (IsDilation receiver)

/-- arXiv:quant-ph/0212066v3, PDF pp.10--11, Lemma 2, (13),(24).
The state is the full postattack state before the final controlled Hadamards;
no independence across pairs or coins is assumed. -/
theorem balanced_attack_phase_bit_gap
    (delta : ℝ) (hdelta : 0 ≤ delta ∧ delta ≤ 1 / 2)
    (rho : (n : ℕ) → Matrix (PairCoinBits n) (PairCoinBits n) ℂ)
    (hstate : ∀ n, IsDensityMatrix (rho n))
    (hbalanced : ExponentiallySmall
      (fun n => coinXFailure (traceLeft (rho n)) delta)) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ExponentiallySmall (fun n => phaseBitGapFailure (rho n) delta epsilon) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P99

end
