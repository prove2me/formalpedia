-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c01
-- name    : TaoFivePrimes.ros_chain_c01
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-10-04T11:10:45.701986+00:00
-- url     : https://prove2.me/theorems/712f23d3-1bdf-4920-b134-a207742aff59
-- title:
--   Rosser-Schoenfeld product bound certificate: (612809, 2875497]
-- statement:
--   Segment c01 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (612809, 2875497]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(612809) >= 3167031598261921, it exports the outgoing state 10^15 * logProd(2875497) >= 3276723638116522 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 612809 < x <= 2875497. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c01 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (3167031598261921 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 612809) :
    (3276723638116522 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 2875497 ∧
      (∀ x : ℝ, (612809 : ℝ) < x → x ≤ (2875497 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
