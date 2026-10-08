-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c13
-- name    : TaoFivePrimes.ros_chain_c13
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-04T11:12:52.74998+00:00
-- url     : https://prove2.me/theorems/4f71d85a-217b-436f-b0aa-5a6ed75505a1
-- title:
--   Rosser-Schoenfeld product bound certificate: (32888396, 35748293]
-- statement:
--   Segment c13 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (32888396, 35748293]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(32888396) >= 3428432446423729, it exports the outgoing state 10^15 * logProd(35748293) >= 3433232788381885 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 32888396 < x <= 35748293. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c13 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3428432446423729 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 32888396) :
    (3433232788381885 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 35748293 ∧
      (∀ x : ℝ, (32888396 : ℝ) < x → x ≤ (35748293 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
