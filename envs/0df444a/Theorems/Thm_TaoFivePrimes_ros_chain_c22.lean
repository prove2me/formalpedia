-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c22
-- name    : TaoFivePrimes.ros_chain_c22
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-04T11:13:31.354901+00:00
-- url     : https://prove2.me/theorems/ae227649-0c25-4a43-a3dd-dee0e5e432fd
-- title:
--   Rosser-Schoenfeld product bound certificate: (56060255, 58410956]
-- statement:
--   Segment c22 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (56060255, 58410956]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(56060255) >= 3458772647671163, it exports the outgoing state 10^15 * logProd(58410956) >= 3461073404553119 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 56060255 < x <= 58410956. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c22 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3458772647671163 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 56060255) :
    (3461073404553119 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 58410956 ∧
      (∀ x : ℝ, (56060255 : ℝ) < x → x ≤ (58410956 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
