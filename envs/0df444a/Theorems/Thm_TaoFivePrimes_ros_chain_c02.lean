-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c02
-- name    : TaoFivePrimes.ros_chain_c02
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:11:02.546494+00:00
-- url     : https://prove2.me/theorems/b8004a23-5ddb-4718-b6d2-ae08bc5a283c
-- title:
--   Rosser-Schoenfeld product bound certificate: (2875497, 5417351]
-- statement:
--   Segment c02 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (2875497, 5417351]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(2875497) >= 3276723638116522, it exports the outgoing state 10^15 * logProd(5417351) >= 3318419797553588 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 2875497 < x <= 5417351. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c02 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3276723638116522 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 2875497) :
    (3318419797553588 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 5417351 ∧
      (∀ x : ℝ, (2875497 : ℝ) < x → x ≤ (5417351 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
