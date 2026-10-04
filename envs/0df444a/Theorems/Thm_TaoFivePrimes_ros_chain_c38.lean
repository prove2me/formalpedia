-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c38
-- name    : TaoFivePrimes.ros_chain_c38
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:14:46.973404+00:00
-- url     : https://prove2.me/theorems/9676e7d7-491a-412c-8229-403a4fa156bb
-- title:
--   Rosser-Schoenfeld product bound certificate: (94416971, 96779954]
-- statement:
--   Segment c38 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (94416971, 96779954]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(94416971) >= 3487569337793548, it exports the outgoing state 10^15 * logProd(96779954) >= 3488916032968464 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 94416971 < x <= 96779954. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c38 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3487569337793548 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 94416971) :
    (3488916032968464 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 96779954 ∧
      (∀ x : ℝ, (94416971 : ℝ) < x → x ≤ (96779954 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
