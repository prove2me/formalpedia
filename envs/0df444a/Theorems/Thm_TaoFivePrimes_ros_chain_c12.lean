-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c12
-- name    : TaoFivePrimes.ros_chain_c12
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:12:46.819657+00:00
-- url     : https://prove2.me/theorems/2f586a09-59bb-4070-810f-e765d701d3b1
-- title:
--   Rosser-Schoenfeld product bound certificate: (30536279, 32888396]
-- statement:
--   Segment c12 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (30536279, 32888396]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(30536279) >= 3424137493192315, it exports the outgoing state 10^15 * logProd(32888396) >= 3428432446423729 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 30536279 < x <= 32888396. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c12 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3424137493192315 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 30536279) :
    (3428432446423729 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 32888396 ∧
      (∀ x : ℝ, (30536279 : ℝ) < x → x ≤ (32888396 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
