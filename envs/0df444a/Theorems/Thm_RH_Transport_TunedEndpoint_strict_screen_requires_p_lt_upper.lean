-- Prove2me | Theorems.Thm_RH_Transport_TunedEndpoint_strict_screen_requires_p_lt_upper
-- name    : RH.Transport.TunedEndpoint.strict_screen_requires_p_lt_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T23:00:28.089668+00:00
-- url     : https://prove2.me/theorems/44c37970-b7ec-4e5e-8535-fec6f1589086
-- title:
--   Tuned Endpoint: strict screen requires p lt upper
-- statement:
--   This screen upper bound allows arbitrary b, but covers only the stated
--   geometry and balanced count formula, not other methods or count estimates.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedEndpoint.lean#L1443-L1451
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedEndpoint.lean#L1443-L1451

import Definitions.Def_Transport_Endpoint
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_TunedEndpoint
import Theorems.Thm_RH_Transport_Endpoint_strict_screen_requires_p_lt_upper

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open RH RH.Transport RH.Transport.TunedEndpoint
noncomputable section

theorem RH.Transport.TunedEndpoint.strict_screen_requires_p_lt_upper {p b : ℝ}
    (hgood : ∀ δ x : ℝ, (1 / 50 : ℝ) ≤ δ → δ ≤ 3 / 4 →
      0 ≤ x → x ≤ 1 / 2 → generalEndpointExponent p b δ x < 0) :
    p < screenUpper := by sorry
