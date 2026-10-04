-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c29
-- name    : TaoFivePrimes.ros_chain_c29
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:14:11.891543+00:00
-- url     : https://prove2.me/theorems/ce60772e-676c-48c5-add1-a880f89cdfc1
-- title:
--   Rosser-Schoenfeld product bound certificate: (73123461, 75502135]
-- statement:
--   Segment c29 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (73123461, 75502135]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(73123461) >= 3473558937346760, it exports the outgoing state 10^15 * logProd(75502135) >= 3475324939988510 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 73123461 < x <= 75502135. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c29 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3473558937346760 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 73123461) :
    (3475324939988510 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 75502135 ∧
      (∀ x : ℝ, (73123461 : ℝ) < x → x ≤ (75502135 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
