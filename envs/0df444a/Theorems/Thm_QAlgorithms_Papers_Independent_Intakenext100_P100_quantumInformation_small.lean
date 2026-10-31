-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P100_quantumInformation_small
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P100.quantumInformation_small
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:25:35.475541+00:00
-- url     : https://prove2.me/theorems/17e55e94-5322-428a-b788-335c7bb84f41
-- title:
--   Quantum mutual information controlled by small measured correlation
-- statement:
--   Let $d\ge2$, let $d'<2d$ be the least prime power at least $d$, and let $\rho$ be a density matrix on $\mathbb C^d\otimes\mathbb C^d$. Define $I_q(\rho)=S(\rho_A)+S(\rho_B)-S(\rho)$ using von Neumann entropies in bits, and set $x=(d'+1)^2\sqrt{2\ln(2)I_c(\rho)}$. If
--   $$I_c(\rho)\le\frac{1}{6\ln(2)(d'+1)^2},$$
--   then the printed standalone estimate is
--   $$I_q(\rho)\le2x\log_2d-x\log_2x.$$
--   The zero term is interpreted continuously. This estimate is the initial-state information bound used in the communication theorem.
-- source:
--   Locking classical correlation in quantum states, arXiv:quant-ph/0303088v1, PDF p. 6, Estimate after Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P100

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P100

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6, standalone estimate following Lemma 1: quantum mutual information
bounded by the printed refined error. Source issue S02 applies to the threshold.
The minimum prime-power condition is inherited from this appendix section. -/
theorem quantumInformation_small {d dp : ℕ} (hd : 2 ≤ d)
    (hprime : IsLeastPrimePowerAbove d dp) (hupper : dp < 2*d)
    (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (hsmall : lockingMeasuredInformation rho ≤ 1 / (6 * Real.log 2) / ((dp : ℝ)+1)^2) :
    Support50.P39.quantumMutualInformation rho ≤ refinedError d dp rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P100

end
