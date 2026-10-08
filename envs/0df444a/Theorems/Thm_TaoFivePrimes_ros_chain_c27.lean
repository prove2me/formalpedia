-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c27
-- name    : TaoFivePrimes.ros_chain_c27
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-04T11:13:57.995749+00:00
-- url     : https://prove2.me/theorems/d57ba794-bb1f-4501-a896-a5384922daf7
-- title:
--   Rosser-Schoenfeld product bound certificate: (68365271, 70740573]
-- statement:
--   Segment c27 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (68365271, 70740573]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(68365271) >= 3469835283342230, it exports the outgoing state 10^15 * logProd(70740573) >= 3471726614209997 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 68365271 < x <= 70740573. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c27 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3469835283342230 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 68365271) :
    (3471726614209997 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 70740573 ∧
      (∀ x : ℝ, (68365271 : ℝ) < x → x ≤ (70740573 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
