-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P100_smallCorrelation_appendix
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P100.smallCorrelation_appendix
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:22:31.238472+00:00
-- url     : https://prove2.me/theorems/7290fede-a241-4a85-ad3a-16661566c314
-- title:
--   Appendix small-correlation communication bounds
-- statement:
--   Let $d\ge2$ and let $d'<2d$ be the least prime power at least $d$, with prime powers understood as $p^n$ for prime $p$ and integer $n\ge1$. Let $\rho$ be a density matrix on $\mathbb C^d\otimes\mathbb C^d$ and let $\rho'$ be its actual output after at most $l\ge0$ transmitted qubits in a finite two-way protocol with arbitrary local operations and no extra shared resource. Put $s=\sqrt{2\ln(2)I_c(\rho)}$, $x=(d'+1)^2s$, and $\eta(x)=-x\log_2x$, with $\eta(0)=0$. If
--   $$I_c(\rho)\le\frac{1}{6\ln(2)(d'+1)^2},$$
--   then both printed bounds hold:
--   $$I_c(\rho')-I_c(\rho)\le2l+2x\log_2d+\eta(x),$$
--   $$I_c(\rho')-I_c(\rho)\le2l-(d'+1)^2s\log_2s.$$
--   These are the refined and simplified appendix versions of the small-correlation estimate.
-- source:
--   Locking classical correlation in quantum states, arXiv:quant-ph/0303088v1, PDF p. 6, Appendix Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P100

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P100

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6, Theorem 2, APPENDIX version: BOTH printed inequalities, least
prime power and squared denominator retained. Source issue S02 applies. -/
theorem smallCorrelation_appendix {d dp a b : ℕ} (hd : 2 ≤ d)
    (hprime : IsLeastPrimePowerAbove d dp) (hupper : dp < 2*d)
    (ha : 0 < a) (hb : 0 < b)
    (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (rhoPrime : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (l : ℕ) (hprotocol : QuantumObtainable l rho rhoPrime)
    (hsmall : lockingMeasuredInformation rho ≤ 1 / (6 * Real.log 2) / ((dp : ℝ)+1)^2) :
    (lockingMeasuredInformation rhoPrime - lockingMeasuredInformation rho ≤
      2 * (l : ℝ) + refinedError d dp rho) ∧
    (lockingMeasuredInformation rhoPrime - lockingMeasuredInformation rho ≤
      2 * (l : ℝ) - ((dp : ℝ)+1)^2 * correlationRoot rho *
        Real.logb 2 (correlationRoot rho)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P100

end
