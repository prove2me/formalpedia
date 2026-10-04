-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c03
-- name    : TaoFivePrimes.ros_chain_c03
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:11:25.119785+00:00
-- url     : https://prove2.me/theorems/71dfe862-6ee1-4637-9e3d-fe0458e3957a
-- title:
--   Rosser-Schoenfeld product bound certificate: (5417351, 8055775]
-- statement:
--   Segment c03 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (5417351, 8055775]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(5417351) >= 3318419797553588, it exports the outgoing state 10^15 * logProd(8055775) >= 3343673084555015 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 5417351 < x <= 8055775. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c03 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3318419797553588 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 5417351) :
    (3343673084555015 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 8055775 ∧
      (∀ x : ℝ, (5417351 : ℝ) < x → x ≤ (8055775 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
