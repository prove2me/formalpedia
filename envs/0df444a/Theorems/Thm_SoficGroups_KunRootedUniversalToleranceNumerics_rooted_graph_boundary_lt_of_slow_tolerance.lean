-- Prove2me | Theorems.Thm_SoficGroups_KunRootedUniversalToleranceNumerics_rooted_graph_boundary_lt_of_slow_tolerance
-- name    : SoficGroups.KunRootedUniversalToleranceNumerics.rooted_graph_boundary_lt_of_slow_tolerance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/b864c3c3-d401-4487-96af-01013fdac4ec
-- title:
--   SoficGroups.KunRootedUniversalToleranceNumerics.rooted_graph_boundary_lt_of_slow_tolerance
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedUniversalToleranceNumerics

theorem SoficGroups.KunRootedUniversalToleranceNumerics.rooted_graph_boundary_lt_of_slow_tolerance
    {h d q t N b c e : ℝ}
    (hh : 0 < h) (hd : 0 < d) (hq : q < 1)
    (ht : 0 < t)
    (hbad : 2 * d * b ≤ t)
    (hmissing : N - 2 * b ≤ c)
    (hboundary : e ≤ 3 * t)
    (hslow :
      5 * (4 + h *
        (216 / (d * (1 - q) ^ 2) + 1 / d)) * t ≤ h * N) :
    e < (d * (1 - q) ^ 2 / 288) * c := by sorry
