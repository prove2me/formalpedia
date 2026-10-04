-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c31
-- name    : TaoFivePrimes.ros_chain_c31
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:14:21.288994+00:00
-- url     : https://prove2.me/theorems/68194554-8c21-4b60-906d-aead0d2f8064
-- title:
--   Rosser-Schoenfeld product bound certificate: (77889202, 80252338]
-- statement:
--   Segment c31 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (77889202, 80252338]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(77889202) >= 3477037521010666, it exports the outgoing state 10^15 * logProd(80252338) >= 3478679231144152 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 77889202 < x <= 80252338. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c31 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3477037521010666 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 77889202) :
    (3478679231144152 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 80252338 ∧
      (∀ x : ℝ, (77889202 : ℝ) < x → x ≤ (80252338 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
