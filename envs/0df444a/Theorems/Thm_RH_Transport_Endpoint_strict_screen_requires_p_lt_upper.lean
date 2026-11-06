-- Prove2me | Theorems.Thm_RH_Transport_Endpoint_strict_screen_requires_p_lt_upper
-- name    : RH.Transport.Endpoint.strict_screen_requires_p_lt_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:25:28.18453+00:00
-- url     : https://prove2.me/theorems/724a6827-90f8-4a33-92d4-c3ca9a4f8a0d
-- title:
--   Endpoint: strict screen requires p lt upper
-- statement:
--   Any p passing the full-domain strict endpoint screen is below this
--   upper bound. This is not an upper bound for other geometries or methods.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Endpoint.lean#L1298-L1306
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Endpoint.lean#L1298-L1306

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Endpoint
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open RH RH.Transport RH.Transport.Endpoint
noncomputable section

theorem RH.Transport.Endpoint.strict_screen_requires_p_lt_upper {p : ℝ}
    (hgood : ∀ δ x : ℝ, (1 / 50 : ℝ) ≤ δ → δ ≤ 3 / 4 →
      0 ≤ x → x ≤ 1 / 2 → generalEndpointExponent p δ x < 0) :
    p < screenUpper := by sorry
