-- Prove2me | Theorems.Thm_WeilDefect_RPB108_low_schur_lower_of_norm_bound
-- name    : WeilDefect.RPB108.low_schur_lower_of_norm_bound
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:54:56.895036+00:00
-- url     : https://prove2.me/theorems/d50dd4e3-f6cf-47b9-b1a3-e31ee098d3bf
-- title:
--   Low Schur floor from norm bounds
-- statement:
--   For a complex inner-product space E, continuous complex-linear T, vector r and real k,P,n,A, assume k>0, ‖T‖≤1/k, ‖r‖²≤P and A+P/k≤n. Then A≤n−Re⟨r,Tr⟩.
--
--   Exact native statement, definitions and coordinate order are preserved. Original-form realization attachments are unproved future formalization; complete 1.06 positivity, global continuation and RH are not established.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/SchurBounds.lean#L19-L26; exact native theorem WeilDefect.RPB108.low_schur_lower_of_norm_bound. SHA256 559f8c972633086de1625a34c0ae03fa96d241415c6b33e4c028839fb43e7de7. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.
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

theorem WeilDefect.RPB108.low_schur_lower_of_norm_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →L[ℂ] E) (r : E) (k P native A : ℝ)
    (hk : 0 < k) (hT : ‖T‖ ≤ 1/k) (hr : ‖r‖^2 ≤ P)
    (hnative : A+P/k ≤ native) : A ≤ native-(inner ℂ r (T r)).re := by sorry
