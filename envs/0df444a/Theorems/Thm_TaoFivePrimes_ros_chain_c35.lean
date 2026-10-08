-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c35
-- name    : TaoFivePrimes.ros_chain_c35
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-04T11:14:26.203216+00:00
-- url     : https://prove2.me/theorems/767881d2-0e37-4e53-a0b0-c539afd10453
-- title:
--   Rosser-Schoenfeld product bound certificate: (87377899, 89738650]
-- statement:
--   Segment c35 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (87377899, 89738650]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(87377899) >= 3483342627371999, it exports the outgoing state 10^15 * logProd(89738650) >= 3484798196139029 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 87377899 < x <= 89738650. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c35 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3483342627371999 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 87377899) :
    (3484798196139029 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 89738650 ∧
      (∀ x : ℝ, (87377899 : ℝ) < x → x ≤ (89738650 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
