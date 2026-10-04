-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c14
-- name    : TaoFivePrimes.ros_chain_c14
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:13:02.185918+00:00
-- url     : https://prove2.me/theorems/7086a9eb-ef86-4f1b-9312-3de0b5ae72fa
-- title:
--   Rosser-Schoenfeld product bound certificate: (35748293, 38490299]
-- statement:
--   Segment c14 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (35748293, 38490299]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(35748293) >= 3433232788381885, it exports the outgoing state 10^15 * logProd(38490299) >= 3437474091343333 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 35748293 < x <= 38490299. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c14 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3433232788381885 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 35748293) :
    (3437474091343333 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 38490299 ∧
      (∀ x : ℝ, (35748293 : ℝ) < x → x ≤ (38490299 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
