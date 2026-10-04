-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c09
-- name    : TaoFivePrimes.ros_chain_c09
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:12:52.100269+00:00
-- url     : https://prove2.me/theorems/5f88ff03-7f1d-40e1-ba48-a06c6abb8e5e
-- title:
--   Rosser-Schoenfeld product bound certificate: (21974447, 24816081]
-- statement:
--   Segment c09 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (21974447, 24816081]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(21974447) >= 3404863595897352, it exports the outgoing state 10^15 * logProd(24816081) >= 3412029848331588 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 21974447 < x <= 24816081. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c09 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3404863595897352 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 21974447) :
    (3412029848331588 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 24816081 ∧
      (∀ x : ℝ, (21974447 : ℝ) < x → x ≤ (24816081 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
