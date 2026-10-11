-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Odd_actual_low_schur_lower
-- name    : WeilDefect.RPB108.DNE27Odd.actual_low_schur_lower
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:55:25.123932+00:00
-- url     : https://prove2.me/theorems/6d500e25-089b-41df-baf5-c6faf53d3af9
-- title:
--   DNE27 odd — Actual low Schur floor
-- statement:
--   Use the exact native parity data and k=11/25. For T, four actual sources σ and real lowDiag, assume ‖T‖≤1/k, ‖σ_0‖²≤sourceSquare_0 and lowNativeLower≤lowDiag. Then nativeLow≤lowDiag−Re⟨σ_0,Tσ_0⟩. The exact rational threshold identity is proved inside this solution.
--
--   Parity: odd.
--
--   Exact native statement, definitions and coordinate order are preserved. Original-form realization attachments are unproved future formalization; complete 1.06 positivity, global continuation and RH are not established.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27SchurBounds.lean#L123-L133; exact native theorem WeilDefect.RPB108.DNE27Odd.actual_low_schur_lower. SHA256 3565e26e8ff2272bd4092d03e9f5786009a91127fe867a754238fbd334606891. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_DNE27MixedEnergy_Odd
import Definitions.Def_RPB108_DNE27Numerics_Odd
import Definitions.Def_RPB108_DNE27SchurBounds_Odd
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Odd

theorem WeilDefect.RPB108.DNE27Odd.actual_low_schur_lower {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →L[ℂ] E) (source : Fin 4 → E) (lowDiag : ℝ)
    (hT : ‖T‖ ≤ 1/highFloor) (hsource0 : ‖source 0‖^2 ≤ sourceSquare 0)
    (hlow : lowNativeLower ≤ lowDiag) : nativeLow ≤ actualLowSchur T source lowDiag := by sorry
