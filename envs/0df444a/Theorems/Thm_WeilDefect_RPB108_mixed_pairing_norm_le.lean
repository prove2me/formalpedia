-- Prove2me | Theorems.Thm_WeilDefect_RPB108_mixed_pairing_norm_le
-- name    : WeilDefect.RPB108.mixed_pairing_norm_le
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T03:59:25.991719+00:00
-- url     : https://prove2.me/theorems/3c114b2f-571d-4748-a489-0bcb965ab680
-- title:
--   Mixed pairing bound against actual energy
-- statement:
--   Let $p,q\in\mathbb C$ and $a,b,V,M\in\mathbb R$. Assume $a,b,V\ge0$, $|p|^2\le aV$, $|q|^2\le bV$, and $\sqrt a+\sqrt b\le M$. Then
--
--   $$|p-q|\le M\sqrt V.$$
--
--   Here $V$ is the actual retained energy. The result combines independent pairing-square bounds via the triangle inequality.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/MixedPairing.lean#L14-L32; exact native theorem WeilDefect.RPB108.mixed_pairing_norm_le. SHA256 a93c990b29d50c5536f57ca66d5750c92cbb38320e8b1188887c2cfdfbf85428. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem WeilDefect.RPB108.mixed_pairing_norm_le (p q : ℂ) (a b V M : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hV : 0 ≤ V)
    (hp : ‖p‖^2 ≤ a*V) (hq : ‖q‖^2 ≤ b*V)
    (hM : Real.sqrt a+Real.sqrt b ≤ M) :
    ‖p-q‖ ≤ M*Real.sqrt V := by sorry
