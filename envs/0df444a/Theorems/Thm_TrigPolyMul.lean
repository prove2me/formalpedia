-- Prove2me | Theorems.Thm_TrigPolyMul
-- name    : TrigPolyMul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T15:13:32.069995+00:00
-- url     : https://prove2.me/theorems/f5b839a1-1ab2-4523-a2c2-859b055cec1e
-- title:
--   Trig Poly Mul: Trig Poly Mul
-- statement:
--   The pointwise product of a real trigonometric polynomial of degree at most
--   `m` and one of degree at most `l` is a real trigonometric polynomial of degree
--   at most `m + l`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TrigPolyMul.lean#L10-L143
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TrigPolyMul.lean#L10-L143

module
public import Definitions.Def_PHarmonicPoly_TrigPolyLe
public import Definitions.Def_PHarmonicPoly_TrigPolyMul
set_option autoImplicit false
@[expose] public section
public section

theorem TrigPolyMul {m l : ℕ} {S T : ℝ → ℝ} (hS : TrigPolyLe m S)
    (hT : TrigPolyLe l T) :
    TrigPolyLe (m + l) (fun t => S t * T t) := by sorry
