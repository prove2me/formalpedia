-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c36
-- name    : TaoFivePrimes.ros_chain_c36
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-04T11:14:37.72466+00:00
-- url     : https://prove2.me/theorems/0d40012d-6e32-4ea7-8d05-24e04dfd4100
-- title:
--   Rosser-Schoenfeld product bound certificate: (89738650, 92086102]
-- statement:
--   Segment c36 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (89738650, 92086102]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(89738650) >= 3484798196139029, it exports the outgoing state 10^15 * logProd(92086102) >= 3486208334321301 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 89738650 < x <= 92086102. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c36 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3484798196139029 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 89738650) :
    (3486208334321301 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 92086102 ∧
      (∀ x : ℝ, (89738650 : ℝ) < x → x ≤ (92086102 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
