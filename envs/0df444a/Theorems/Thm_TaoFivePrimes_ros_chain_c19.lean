-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c19
-- name    : TaoFivePrimes.ros_chain_c19
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-04T11:13:28.773112+00:00
-- url     : https://prove2.me/theorems/19f80495-4286-4911-b522-ec20bc7752cd
-- title:
--   Rosser-Schoenfeld product bound certificate: (48455251, 50789637]
-- statement:
--   Segment c19 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (48455251, 50789637]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(48455251) >= 3450568959803566, it exports the outgoing state 10^15 * logProd(50789637) >= 3453227328165421 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 48455251 < x <= 50789637. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c19 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3450568959803566 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 48455251) :
    (3453227328165421 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 50789637 ∧
      (∀ x : ℝ, (48455251 : ℝ) < x → x ≤ (50789637 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
