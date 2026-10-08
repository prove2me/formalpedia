-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c23
-- name    : TaoFivePrimes.ros_chain_c23
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-04T11:13:45.443545+00:00
-- url     : https://prove2.me/theorems/613e78c9-415e-4b9c-9218-deed7d410a37
-- title:
--   Rosser-Schoenfeld product bound certificate: (58410956, 60768727]
-- statement:
--   Segment c23 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (58410956, 60768727]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(58410956) >= 3461073404553119, it exports the outgoing state 10^15 * logProd(60768727) >= 3463284588084618 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 58410956 < x <= 60768727. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c23 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3461073404553119 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 58410956) :
    (3463284588084618 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 60768727 ∧
      (∀ x : ℝ, (58410956 : ℝ) < x → x ≤ (60768727 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
