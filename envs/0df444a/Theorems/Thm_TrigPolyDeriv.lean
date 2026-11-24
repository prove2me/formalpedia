-- Prove2me | Theorems.Thm_TrigPolyDeriv
-- name    : TrigPolyDeriv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T15:27:33.466796+00:00
-- url     : https://prove2.me/theorems/6453f53e-45a2-4238-b940-086c9a3ecdfe
-- title:
--   Trig Poly Deriv: Trig Poly Deriv
-- statement:
--   The derivative of a real trigonometric polynomial of degree at most `m` is
--   again a real trigonometric polynomial of degree at most `m`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TrigPolyDeriv.lean#L10-L40
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TrigPolyDeriv.lean#L10-L40

module
public import Definitions.Def_PHarmonicPoly_TrigPolyLe
public import Definitions.Def_PHarmonicPoly_TrigPolySmooth
public import Definitions.Def_PHarmonicPoly_TrigPolyDeriv
public import Theorems.Thm_TrigPolySmooth

set_option autoImplicit false
@[expose] public section
public section

theorem TrigPolyDeriv {m : ℕ} {T : ℝ → ℝ} (hT : TrigPolyLe m T) :
    TrigPolyLe m (deriv T) := by sorry
