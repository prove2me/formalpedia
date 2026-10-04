-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c07
-- name    : TaoFivePrimes.ros_chain_c07
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:12:00.72497+00:00
-- url     : https://prove2.me/theorems/86f89552-1f16-4bd9-9949-1cb31ff200fc
-- title:
--   Rosser-Schoenfeld product bound certificate: (16295078, 19124809]
-- statement:
--   Segment c07 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (16295078, 19124809]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(16295078) >= 3387014732239145, it exports the outgoing state 10^15 * logProd(19124809) >= 3396612041201769 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 16295078 < x <= 19124809. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c07 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3387014732239145 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 16295078) :
    (3396612041201769 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 19124809 ∧
      (∀ x : ℝ, (16295078 : ℝ) < x → x ≤ (19124809 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
