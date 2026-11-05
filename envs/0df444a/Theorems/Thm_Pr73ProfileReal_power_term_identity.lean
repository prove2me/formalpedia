-- Prove2me | Theorems.Thm_Pr73ProfileReal_power_term_identity
-- name    : Pr73ProfileReal.power_term_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.688206+00:00
-- url     : https://prove2.me/theorems/dbd78885-9912-49aa-a5a2-92ffc0a98e5a
-- title:
--   Pr73ProfileReal: Power term identity
-- statement:
--   Exact term identity used to express the result in recurrence form.
--
--   Real analytic contraction inequalities derived from the pinned PR73 rational profile. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/full-transfer/latest-analytic/Pr73ProfileReal.lean#L73-L86). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/full-transfer/latest-analytic/Pr73ProfileReal.lean#L73-L86 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_Pr73ProfileCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Pr73ProfileReal
set_option autoImplicit true
open Pr73ProfileReal
open AnalyticEnclosures Pr73ProfileCertificate

theorem Pr73ProfileReal.power_term_identity (n t m W a : ℝ) (ht : 0 < t) (hm : 0 < m) :
    (n / W) * (t / m) ^ (1 - a) =
      (n * t / (m * W)) * Real.exp (a * Real.log (m / t)) := by sorry
