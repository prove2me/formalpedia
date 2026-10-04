-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c04
-- name    : TaoFivePrimes.ros_chain_c04
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:11:32.414985+00:00
-- url     : https://prove2.me/theorems/b3a13a97-0f48-4890-8c98-00a178ba9d67
-- title:
--   Rosser-Schoenfeld product bound certificate: (8055775, 10737397]
-- statement:
--   Segment c04 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (8055775, 10737397]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(8055775) >= 3343673084555015, it exports the outgoing state 10^15 * logProd(10737397) >= 3361582274225459 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 8055775 < x <= 10737397. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c04 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3343673084555015 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 8055775) :
    (3361582274225459 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 10737397 ∧
      (∀ x : ℝ, (8055775 : ℝ) < x → x ≤ (10737397 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
