-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c17
-- name    : TaoFivePrimes.ros_chain_c17
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:13:04.960333+00:00
-- url     : https://prove2.me/theorems/f44d484d-4e62-4343-b31f-cf79c82c16fe
-- title:
--   Rosser-Schoenfeld product bound certificate: (43185705, 46089126]
-- statement:
--   Segment c17 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (43185705, 46089126]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(43185705) >= 3444042908641756, it exports the outgoing state 10^15 * logProd(46089126) >= 3447740640073195 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 43185705 < x <= 46089126. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c17 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3444042908641756 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 43185705) :
    (3447740640073195 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 46089126 ∧
      (∀ x : ℝ, (43185705 : ℝ) < x → x ≤ (46089126 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
