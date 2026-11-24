-- Prove2me | Theorems.Thm_TrigPolyEvenPart
-- name    : TrigPolyEvenPart
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T15:13:33.497253+00:00
-- url     : https://prove2.me/theorems/64cebea3-c8bf-4d37-b07b-1941ee26efec
-- title:
--   Trig Poly Even Part: Trig Poly Even Part
-- statement:
--   The even part of a real trigonometric polynomial of degree at most `m` is a
--   polynomial of degree at most `m` evaluated at `cos t`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TrigPolyEvenPart.lean#L9-L45
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TrigPolyEvenPart.lean#L9-L45

module
public import Definitions.Def_PHarmonicPoly_TrigPolyLe
public import Definitions.Def_PHarmonicPoly_TrigPolyEvenPart
set_option autoImplicit false
@[expose] public section
public section

theorem TrigPolyEvenPart {m : ℕ} {T : ℝ → ℝ} (hT : TrigPolyLe m T) :
    ∃ P : Polynomial ℝ, P.degree ≤ (m : ℕ) ∧
      ∀ t : ℝ, P.eval (Real.cos t) = (T t + T (-t)) / 2 := by sorry
