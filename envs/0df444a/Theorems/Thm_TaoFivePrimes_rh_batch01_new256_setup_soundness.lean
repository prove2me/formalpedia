-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_new256_setup_soundness
-- name    : TaoFivePrimes.rh_batch01_new256_setup_soundness
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T13:31:13.895463+00:00
-- url     : https://prove2.me/theorems/7ce9d921-6ab8-4447-8023-c188a0451b34
-- title:
--   TaoFivePrimes.rh_batch01_new256_setup_soundness
-- statement:
--   Fresh cached inputs enclose the actual center, logarithm, anchor and degree28 polynomial coefficients.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Original mathematical attribution: sometik179, submission c9908072-d99a-4431-aad8-a72c6352619a, and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastWindow256Setup
import Definitions.Def_TaoFivePrimes_RHBatch01New256Common
import Definitions.Def_TaoFivePrimes_RHFastBallFrequencyChecker256
import Definitions.Def_TaoFivePrimes_RHFastPolynomialCircuitSemantics
import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Definitions.Def_TaoFivePrimes_RHFastComplexBallSemantics
import Theorems.Thm_TaoFivePrimes_rh_batch01_new256_setup_arithmetic
import Theorems.Thm_TaoFivePrimes_rh_fast_center_scalar_seed_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_log_center_seed_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_pi_root_ball_seeds
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_rescale_anchor
import Theorems.Thm_TaoFivePrimes_rh_fresh16_anchor_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_polynomial_circuit_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_polynomial_circuit_identity
import Theorems.Thm_TaoFivePrimes_rh_fast_moment_factor_ball_soundness256
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.NormNum
open Complex Finset Polynomial
open RHFastBallArithmetic RHFastBallSemantics RHFastComplexPoly

theorem TaoFivePrimes.rh_batch01_new256_setup_soundness :
 RHFastBallSemantics.encloses RHFastWindow256Setup.D RHBatch01New256Common.anchor (RHFastGaussianWindow.anchor 3289999808) ∧
 RHFastBallSemantics.encloses RHFastWindow256Setup.D RHBatch01New256Common.pi (Real.pi:ℂ) ∧
 RHFastBallSemantics.encloses RHFastWindow256Setup.D RHBatch01New256Common.root ((Real.sqrt (2*Real.pi):ℝ):ℂ) ∧
 RHFastBallSemantics.encloses RHFastWindow256Setup.D RHBatch01New256Common.omega ((RHFastGaussianWindow.omega 3289999808:ℝ):ℂ) ∧
 (∀d:Nat,RHFastBallSemantics.encloses RHFastWindow256Setup.D (RHFastBallFrequencyChecker256.entry RHBatch01New256Common.qs d)
  ((RHFastGaussianWindow.proxyPolynomial 3289999808).coeff d)) ∧
 (∀k:Nat,k<24→RHFastBallSemantics.encloses RHFastWindow256Setup.D (RHFastBallFrequencyChecker256.entry RHBatch01New256Common.factors k)
  (((-Real.pi:ℝ):ℂ)^k/(k.factorial:ℂ))) := by sorry
