-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c34
-- name    : TaoFivePrimes.ros_chain_c34
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-04T11:14:32.272853+00:00
-- url     : https://prove2.me/theorems/369878b6-8e9c-418b-b9cb-d9f3bdc0d28f
-- title:
--   Rosser-Schoenfeld product bound certificate: (85012902, 87377899]
-- statement:
--   Segment c34 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (85012902, 87377899]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(85012902) >= 3481841241769495, it exports the outgoing state 10^15 * logProd(87377899) >= 3483342627371999 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 85012902 < x <= 87377899. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c34 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3481841241769495 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 85012902) :
    (3483342627371999 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 87377899 ∧
      (∀ x : ℝ, (85012902 : ℝ) < x → x ≤ (87377899 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
