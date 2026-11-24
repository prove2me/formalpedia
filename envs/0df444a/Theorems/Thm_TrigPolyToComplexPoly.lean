-- Prove2me | Theorems.Thm_TrigPolyToComplexPoly
-- name    : TrigPolyToComplexPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T15:14:51.603114+00:00
-- url     : https://prove2.me/theorems/2c0cdee1-8765-4f5c-b332-efcccce1dc49
-- title:
--   Trig Poly To Complex Poly: Trig Poly To Complex Poly
-- statement:
--   A real trigonometric polynomial `T` of degree at most `m` is carried to a
--   complex polynomial `Q` of degree at most `2*m` by
--   `Q (e ^ (i t)) = e ^ (i m t) * T t`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TrigPolyToComplexPoly.lean#L10-L98
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TrigPolyToComplexPoly.lean#L10-L98

module
public import Definitions.Def_PHarmonicPoly_TrigPolyLe
public import Definitions.Def_PHarmonicPoly_TrigPolyToComplexPoly
set_option autoImplicit false
@[expose] public section
public section

theorem TrigPolyToComplexPoly {m : ℕ} {T : ℝ → ℝ} (hT : TrigPolyLe m T) :
    ∃ Q : Polynomial ℂ, Q.degree ≤ (2 * m : ℕ) ∧
      ∀ t : ℝ, Q.eval (Complex.exp ((t : ℂ) * Complex.I))
        = Complex.exp ((m : ℂ) * (t : ℂ) * Complex.I) * (T t : ℂ) := by sorry
