-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Even_actual_retained_schur_lower
-- name    : WeilDefect.RPB108.DNE27Even.actual_retained_schur_lower
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:55:45.381482+00:00
-- url     : https://prove2.me/theorems/03aa9431-c8f5-4c73-9240-6743b5f8848b
-- title:
--   DNE27 even — Actual retained Schur floor
-- statement:
--   Use the exact native parity scales and k=11/25. For T, four actual sources σ, real matrices V,G and z in ℂ⁴, assume ‖T‖≤1/k and ⟨σ_(i+1),σ_(j+1)⟩=gramScales_i gramScales_j G_ij for all nine pairs. Put w_i=gramScales_i z_(i+1) and r=Σ_i z_(i+1)σ_(i+1). Then Q_V(w)≤Q_(V+G/k)(w)−Re⟨r,Tr⟩. This requires neither matrix enclosure nor inverse equation; the actual source Gram realization is explicit.
--
--   Parity: even.
--
--   Exact native statement, definitions and coordinate order are preserved. Original-form realization attachments are unproved future formalization; complete 1.06 positivity, global continuation and RH are not established.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27SchurBounds.lean#L42-L55; exact native theorem WeilDefect.RPB108.DNE27Even.actual_retained_schur_lower. SHA256 3565e26e8ff2272bd4092d03e9f5786009a91127fe867a754238fbd334606891. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_DNE27Numerics_Even
import Definitions.Def_RPB108_DNE27SchurBounds_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

theorem WeilDefect.RPB108.DNE27Even.actual_retained_schur_lower {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →L[ℂ] E) (source : Fin 4 → E)
    (V G : Fin 3 → Fin 3 → ℝ) (hT : ‖T‖ ≤ 1/highFloor)
    (hGram : ∀ i j, inner ℂ (source i.succ) (source j.succ) =
      ((gramScales i*gramScales j*G i j : ℝ) : ℂ)) (z : Fin 4 → ℂ) :
    complexGram V (fun i => (gramScales i : ℂ)*z i.succ) ≤
      actualRetainedSchur T source V G z := by sorry
