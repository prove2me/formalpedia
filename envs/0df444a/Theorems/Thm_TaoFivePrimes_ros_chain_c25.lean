-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c25
-- name    : TaoFivePrimes.ros_chain_c25
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-04T11:13:55.104952+00:00
-- url     : https://prove2.me/theorems/4c6e236f-d422-498d-9734-182ca160720f
-- title:
--   Rosser-Schoenfeld product bound certificate: (63100917, 65991971]
-- statement:
--   Segment c25 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (63100917, 65991971]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(63100917) >= 3465381053392159, it exports the outgoing state 10^15 * logProd(65991971) >= 3467872212842771 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 63100917 < x <= 65991971. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c25 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3465381053392159 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 63100917) :
    (3467872212842771 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 65991971 ∧
      (∀ x : ℝ, (63100917 : ℝ) < x → x ≤ (65991971 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
