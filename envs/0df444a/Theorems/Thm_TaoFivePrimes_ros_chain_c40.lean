-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c40
-- name    : TaoFivePrimes.ros_chain_c40
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:14:39.633323+00:00
-- url     : https://prove2.me/theorems/884a4149-f09a-4c81-904f-1348793fdfd8
-- title:
--   Rosser-Schoenfeld product bound certificate: (99147537, 100000000]
-- statement:
--   Segment c40 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (99147537, 100000000]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(99147537) >= 3490229237583226, it exports the outgoing state 10^15 * logProd(100000000) >= 3490693675611438 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 99147537 < x <= 100000000. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c40 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3490229237583226 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 99147537) :
    (3490693675611438 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 100000000 ∧
      (∀ x : ℝ, (99147537 : ℝ) < x → x ≤ (100000000 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
