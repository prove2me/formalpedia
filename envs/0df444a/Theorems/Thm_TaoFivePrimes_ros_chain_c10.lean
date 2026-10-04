-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c10
-- name    : TaoFivePrimes.ros_chain_c10
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:12:26.366668+00:00
-- url     : https://prove2.me/theorems/db949e02-04c6-455b-b7e4-bd9e3e5a1a66
-- title:
--   Rosser-Schoenfeld product bound certificate: (24816081, 27650683]
-- statement:
--   Segment c10 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (24816081, 27650683]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(24816081) >= 3412029848331588, it exports the outgoing state 10^15 * logProd(27650683) >= 3418359072644963 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 24816081 < x <= 27650683. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c10 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3412029848331588 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 24816081) :
    (3418359072644963 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 27650683 ∧
      (∀ x : ℝ, (24816081 : ℝ) < x → x ≤ (27650683 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
