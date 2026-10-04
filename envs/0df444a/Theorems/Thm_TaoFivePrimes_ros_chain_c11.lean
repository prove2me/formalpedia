-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c11
-- name    : TaoFivePrimes.ros_chain_c11
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:12:36.209366+00:00
-- url     : https://prove2.me/theorems/79795c92-9040-4b22-9b7d-ca17705ac563
-- title:
--   Rosser-Schoenfeld product bound certificate: (27650683, 30536279]
-- statement:
--   Segment c11 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (27650683, 30536279]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(27650683) >= 3418359072644963, it exports the outgoing state 10^15 * logProd(30536279) >= 3424137493192315 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 27650683 < x <= 30536279. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c11 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3418359072644963 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 27650683) :
    (3424137493192315 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 30536279 ∧
      (∀ x : ℝ, (27650683 : ℝ) < x → x ≤ (30536279 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
