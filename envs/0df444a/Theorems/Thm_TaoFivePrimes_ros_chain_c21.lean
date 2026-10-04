-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c21
-- name    : TaoFivePrimes.ros_chain_c21
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:13:39.95999+00:00
-- url     : https://prove2.me/theorems/221ab262-cd2e-47e7-9345-17a200801979
-- title:
--   Rosser-Schoenfeld product bound certificate: (53155500, 56060255]
-- statement:
--   Segment c21 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (53155500, 56060255]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(53155500) >= 3455789502770589, it exports the outgoing state 10^15 * logProd(56060255) >= 3458772647671163 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 53155500 < x <= 56060255. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c21 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3455789502770589 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 53155500) :
    (3458772647671163 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 56060255 ∧
      (∀ x : ℝ, (53155500 : ℝ) < x → x ≤ (56060255 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
