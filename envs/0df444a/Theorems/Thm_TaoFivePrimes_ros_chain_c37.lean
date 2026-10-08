-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c37
-- name    : TaoFivePrimes.ros_chain_c37
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-04T11:14:29.458976+00:00
-- url     : https://prove2.me/theorems/deb4225d-2765-4e3c-9c7e-9f234140f5ad
-- title:
--   Rosser-Schoenfeld product bound certificate: (92086102, 94416971]
-- statement:
--   Segment c37 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (92086102, 94416971]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(92086102) >= 3486208334321301, it exports the outgoing state 10^15 * logProd(94416971) >= 3487569337793548 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 92086102 < x <= 94416971. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c37 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3486208334321301 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 92086102) :
    (3487569337793548 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 94416971 ∧
      (∀ x : ℝ, (92086102 : ℝ) < x → x ≤ (94416971 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
