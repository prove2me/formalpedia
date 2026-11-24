-- Prove2me | Theorems.Thm_SecondDerivAtMaxNonpos
-- name    : SecondDerivAtMaxNonpos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T14:57:48.367823+00:00
-- url     : https://prove2.me/theorems/7cd42cd5-3494-4ba7-a09f-05107a9ed258
-- title:
--   Second Deriv At Max Nonpos: Second Deriv At Max Nonpos
-- statement:
--   The second-derivative test at an interior maximum. If a differentiable
--   `g : ℝ → ℝ` attains a global maximum at `0`, and its derivative is itself
--   differentiable at `0` with derivative `L` there, then `L ≤ 0`. Mathlib supplies
--   only the first-order test (`IsLocalMax.deriv_eq_zero`); this is the second-order
--   one.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/SecondDerivAtMaxNonpos.lean#L12-L43
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/SecondDerivAtMaxNonpos.lean#L12-L43

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_SecondDerivAtMaxNonpos
set_option autoImplicit false
@[expose] public section
public section

theorem SecondDerivAtMaxNonpos (g : ℝ → ℝ) (L : ℝ) (hdiff : Differentiable ℝ g)
    (hmax : ∀ σ : ℝ, g σ ≤ g 0) (hDD : HasDerivAt (deriv g) L 0) : L ≤ 0 := by sorry
