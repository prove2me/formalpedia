-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c06
-- name    : TaoFivePrimes.ros_chain_c06
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-04T11:11:49.656631+00:00
-- url     : https://prove2.me/theorems/0a06769b-4b3c-4529-b280-24c9b7fee044
-- title:
--   Rosser-Schoenfeld product bound certificate: (13535626, 16295078]
-- statement:
--   Segment c06 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (13535626, 16295078]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(13535626) >= 3375777222241468, it exports the outgoing state 10^15 * logProd(16295078) >= 3387014732239145 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 13535626 < x <= 16295078. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c06 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3375777222241468 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 13535626) :
    (3387014732239145 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 16295078 ∧
      (∀ x : ℝ, (13535626 : ℝ) < x → x ≤ (16295078 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
