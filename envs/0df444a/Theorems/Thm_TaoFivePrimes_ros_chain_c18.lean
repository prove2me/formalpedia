-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c18
-- name    : TaoFivePrimes.ros_chain_c18
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:13:18.931088+00:00
-- url     : https://prove2.me/theorems/b8f4ef23-46aa-47a7-8f44-4197b8d5fb06
-- title:
--   Rosser-Schoenfeld product bound certificate: (46089126, 48455251]
-- statement:
--   Segment c18 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (46089126, 48455251]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(46089126) >= 3447740640073195, it exports the outgoing state 10^15 * logProd(48455251) >= 3450568959803566 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 46089126 < x <= 48455251. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c18 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3447740640073195 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 46089126) :
    (3450568959803566 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 48455251 ∧
      (∀ x : ℝ, (46089126 : ℝ) < x → x ≤ (48455251 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
