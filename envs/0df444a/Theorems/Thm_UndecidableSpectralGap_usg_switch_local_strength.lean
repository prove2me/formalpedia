-- Prove2me | Theorems.Thm_UndecidableSpectralGap_usg_switch_local_strength
-- name    : UndecidableSpectralGap.usg_switch_local_strength
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-22T18:16:08.791857+00:00
-- url     : https://prove2.me/theorems/b8fcbcf2-491f-49b2-8222-52457058bc1f
-- title:
--   Three-state switch local interaction-strength bound
-- statement:
--   For parameters $0<b\le 1/2$ and $|a|\le b$, the on-site projector, guarded horizontal exchange, and vertical guard of the three-state switch have combined local interaction strength at most one. In symbols,
--
--   $$\|aP\|+2\|G+bF\|+2\|G\|\le 1,$$
--
--   where the displayed expression denotes the model's normalized `localInteractionStrength`. This isolates the finite matrix-norm estimate from the many-body spectral analysis.
-- source:
--   Original auxiliary specialization of the vacuum/occupied-sector construction in Cubitt–Pérez-García–Wolf, arXiv:1502.04573v5, Section 6.2, equations (130a)–(130d); the precise normalization and matrices are those of Definitions.Def_usg_three_state_switch.

import Definitions.Def_usg_three_state_switch

set_option autoImplicit false
open UndecidableSpectralGap

theorem UndecidableSpectralGap.usg_switch_local_strength
    (b a : ℝ) (hb : 0 < b) (hbhalf : b ≤ 1 / 2) (ha : |a| ≤ b) :
    localInteractionStrength ((a : ℂ) • switchProjector)
      (switchGuard + (b : ℂ) • switchExchange) switchGuard ≤ 1 := by sorry
