-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c24
-- name    : TaoFivePrimes.ros_chain_c24
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:13:44.462764+00:00
-- url     : https://prove2.me/theorems/54d522f5-6bc7-4d39-a539-7cb0d0264ec1
-- title:
--   Rosser-Schoenfeld product bound certificate: (60768727, 63100917]
-- statement:
--   Segment c24 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (60768727, 63100917]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(60768727) >= 3463284588084618, it exports the outgoing state 10^15 * logProd(63100917) >= 3465381053392159 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 60768727 < x <= 63100917. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c24 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3463284588084618 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 60768727) :
    (3465381053392159 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 63100917 ∧
      (∀ x : ℝ, (60768727 : ℝ) < x → x ≤ (63100917 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
