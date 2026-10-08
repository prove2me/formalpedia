-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c26
-- name    : TaoFivePrimes.ros_chain_c26
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-04T11:14:06.414983+00:00
-- url     : https://prove2.me/theorems/03974825-fd76-4169-83e0-39bbb8de0867
-- title:
--   Rosser-Schoenfeld product bound certificate: (65991971, 68365271]
-- statement:
--   Segment c26 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (65991971, 68365271]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(65991971) >= 3467872212842771, it exports the outgoing state 10^15 * logProd(68365271) >= 3469835283342230 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 65991971 < x <= 68365271. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c26 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3467872212842771 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 65991971) :
    (3469835283342230 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 68365271 ∧
      (∀ x : ℝ, (65991971 : ℝ) < x → x ≤ (68365271 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
