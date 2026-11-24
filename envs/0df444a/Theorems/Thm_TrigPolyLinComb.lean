-- Prove2me | Theorems.Thm_TrigPolyLinComb
-- name    : TrigPolyLinComb
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T14:41:19.971826+00:00
-- url     : https://prove2.me/theorems/0dce6f84-ed83-4712-880c-e90aeef0ca52
-- title:
--   Trig Poly Lin Comb: Trig Poly Lin Comb
-- statement:
--   Real trigonometric polynomials of degree at most `m` form a linear subspace:
--   a pointwise linear combination of two of them is again one.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TrigPolyLinComb.lean#L9-L16
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TrigPolyLinComb.lean#L9-L16

module
public import Definitions.Def_PHarmonicPoly_TrigPolyLe
public import Definitions.Def_PHarmonicPoly_TrigPolyLinComb
set_option autoImplicit false
@[expose] public section
public section

theorem TrigPolyLinComb {m : ℕ} {S T : ℝ → ℝ} (hS : TrigPolyLe m S)
    (hT : TrigPolyLe m T) (c d : ℝ) :
    TrigPolyLe m (fun t => c * S t + d * T t) := by sorry
