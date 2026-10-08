-- Prove2me | Theorems.Thm_TaoFivePrimes_ros_chain_c00
-- name    : TaoFivePrimes.ros_chain_c00
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-10-04T11:10:29.856103+00:00
-- url     : https://prove2.me/theorems/34456a24-8374-4c81-a20a-d77878f45791
-- title:
--   Rosser-Schoenfeld product bound certificate: (9974, 612809]
-- statement:
--   Segment c00 of the chained kernel certificate for the Rosser-Schoenfeld Mertens product lower bound, spanning the interval (9974, 612809]. Conditionally on e^gamma < 577216170667183/10^15 and on the incoming state 10^15 * logProd(9974) >= 2798773491004910, it exports the outgoing state 10^15 * logProd(612809) >= 3167031598261921 and proves that exp(gamma) * log x < prod_{p <= x} p/(p-1) for every real x with 9974 < x <= 612809. The interval is partitioned into consecutive prime-interval blocks grouped into chained groups; each block inequality is discharged by kernel computation and the groups are chained. The segment is independent of the others: the incoming state is a hypothesis.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_ros_lower

theorem TaoFivePrimes.ros_chain_c00 (hγ : Real.eulerMascheroniConstant < (RosserLower.gammaUpS : ℝ) / (RosserLower.S : ℝ))
    (hstate : (2798773491004910 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 9974) :
    (3167031598261921 : ℝ) ≤ (RosserLower.S : ℝ) * RosserLower.logProd 612809 ∧
      (∀ x : ℝ, (9974 : ℝ) < x → x ≤ (612809 : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < RosserProductCertificate.eulerProduct ⌊x⌋₊) := by sorry
