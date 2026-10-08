-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c32
-- name    : TaoFivePrimes.ros_chain_c32
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-04T11:14:11.353999+00:00
-- url     : https://prove2.me/theorems/046ee34a-b238-4eb3-89f1-7578655a9af3
-- title:
--   Rosser-Schoenfeld product bound certificate: (80252338, 82629481]
-- statement:
--   Segment c32 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (80252338, 82629481]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(80252338) >= 3478679231144152, it exports the outgoing state 10^15 * logProd(82629481) >= 3480283512810665 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 80252338 < x <= 82629481. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c32 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3478679231144152 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 80252338) :
    (3480283512810665 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 82629481 ∧
      (∀ x : ℝ, (80252338 : ℝ) < x → x ≤ (82629481 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
