-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_certificate_fastMul_correct
-- name    : TaoFivePrimes.rh_certificate_fastMul_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-14T09:15:31.982759+00:00
-- url     : https://prove2.me/theorems/fcc26fc7-f923-4102-ab0a-7cd1273c93d9
-- title:
--   TaoFivePrimes.rh_certificate_fastMul_correct
-- statement:
--   The finite recursive Karatsuba-style checker computes the exact natural number product for every recursion budget, split position and pair of operands. This reusable arithmetic theorem supplies no zeta approximation or RH conclusion.
-- source:
--   Scalable certificate-checker investigation for the existing Tao five-primes finite-RH milestone. The surrounding xi/theta certificate project retains attribution to sometik179 (original c9908072-d99a-4431-aad8-a72c6352619a) and theta/Mellin foundations to Gabewhigham. The integer checker is proved directly by the Karatsuba identity and the exact bit-split decomposition in ordinary Lean.

import Definitions.Def_TaoFivePrimes_RHCertificateFastMul

theorem TaoFivePrimes.rh_certificate_fastMul_correct (n k a b : Nat) : RHScalableArithmetic.fastMul n k a b=a*b := by sorry
