-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c08
-- name    : TaoFivePrimes.ros_chain_c08
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-04T11:12:19.867117+00:00
-- url     : https://prove2.me/theorems/09fce0cd-1283-4040-a487-3a1debd398cf
-- title:
--   Rosser-Schoenfeld product bound certificate: (19124809, 21974447]
-- statement:
--   Segment c08 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (19124809, 21974447]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(19124809) >= 3396612041201769, it exports the outgoing state 10^15 * logProd(21974447) >= 3404863595897352 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 19124809 < x <= 21974447. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c08 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3396612041201769 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 19124809) :
    (3404863595897352 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 21974447 ∧
      (∀ x : ℝ, (19124809 : ℝ) < x → x ≤ (21974447 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
