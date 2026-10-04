-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c15
-- name    : TaoFivePrimes.ros_chain_c15
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:13:47.633988+00:00
-- url     : https://prove2.me/theorems/aa3c2cfe-c621-4d06-ab79-f4b57bf65c84
-- title:
--   Rosser-Schoenfeld product bound certificate: (38490299, 40837503]
-- statement:
--   Segment c15 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (38490299, 40837503]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(38490299) >= 3437474091343333, it exports the outgoing state 10^15 * logProd(40837503) >= 3440863107387365 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 38490299 < x <= 40837503. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c15 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3437474091343333 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 38490299) :
    (3440863107387365 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 40837503 ∧
      (∀ x : ℝ, (38490299 : ℝ) < x → x ≤ (40837503 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
