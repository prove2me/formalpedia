-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P100_smallCorrelation_main
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P100.smallCorrelation_main
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:19:09.503119+00:00
-- url     : https://prove2.me/theorems/849c4a71-f969-41f9-b110-e6a7ad45ca2e
-- title:
--   Small initial correlation: main-text communication bound
-- statement:
--   Let $d\ge1$, let $\rho$ be a density matrix on $\mathbb C^d\otimes\mathbb C^d$, and let $\rho'$ be its actual output after a finite two-way protocol transmitting at most $l$ qubits, for an integer $l\ge0$. Local quantum operations, ancillas and disposal are arbitrary; no further shared resource is supplied. Put $s=\sqrt{2\ln(2)I_c(\rho)}$. If
--   $$I_c(\rho)\le\frac{1}{6\ln(2)(d+1)^2},$$
--   then
--   $$I_c(\rho')-I_c(\rho)\le2l-(2d)^2s\log_2s.$$
--   The term $s\log_2s$ is zero at $s=0$. This is the main-text, dimension-dependent bound on unlocking near product states.
-- source:
--   Locking classical correlation in quantum states, arXiv:quant-ph/0303088v1, PDF p. 3, Theorem 2, continued on PDF p. 4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P100

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P100

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3--4, Theorem 2, MAIN-TEXT version. Printed threshold and (2d)^2
are retained without a silent Fannes-domain repair; see source issue S02. -/
theorem smallCorrelation_main {d a b : ℕ} (hd : 0 < d) (ha : 0 < a) (hb : 0 < b)
    (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (rhoPrime : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (l : ℕ) (hprotocol : QuantumObtainable l rho rhoPrime)
    (hsmall : lockingMeasuredInformation rho ≤ 1 / (6 * Real.log 2) / ((d : ℝ)+1)^2) :
    lockingMeasuredInformation rhoPrime - lockingMeasuredInformation rho ≤
      2 * (l : ℝ) - (2 * (d : ℝ))^2 * correlationRoot rho *
        Real.logb 2 (correlationRoot rho) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P100

end
