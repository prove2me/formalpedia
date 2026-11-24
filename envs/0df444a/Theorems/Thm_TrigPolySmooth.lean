-- Prove2me | Theorems.Thm_TrigPolySmooth
-- name    : TrigPolySmooth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T14:41:19.390431+00:00
-- url     : https://prove2.me/theorems/9eb8cb37-beb9-4eb0-b174-50228a2df2ba
-- title:
--   Trig Poly Smooth: Trig Poly Smooth
-- statement:
--   A real trigonometric polynomial of degree at most `m` is real-analytic on
--   `ℝ` (the smoothness exponent `ω` is analyticity).
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TrigPolySmooth.lean#L10-L20
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TrigPolySmooth.lean#L10-L20

module
public import Definitions.Def_PHarmonicPoly_TrigPolyLe
public import Definitions.Def_PHarmonicPoly_TrigPolySmooth
set_option autoImplicit false
@[expose] public section
public section
open scoped ContDiff

theorem TrigPolySmooth {m : ℕ} {T : ℝ → ℝ} (hT : TrigPolyLe m T) :
    ContDiff ℝ ω T := by sorry
