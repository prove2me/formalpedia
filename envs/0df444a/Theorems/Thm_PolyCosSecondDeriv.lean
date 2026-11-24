-- Prove2me | Theorems.Thm_PolyCosSecondDeriv
-- name    : PolyCosSecondDeriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T15:13:45.005171+00:00
-- url     : https://prove2.me/theorems/32c79e7b-4cd8-4fdd-8217-cfc36479ff1c
-- title:
--   Poly Cos Second Deriv: Poly Cos Second Deriv
-- statement:
--   For `P : ℝ[X]` and `G t = P.eval (cos t)`, one has `G'' 0 = -P'(1)`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/PolyCosSecondDeriv.lean#L8-L36
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/PolyCosSecondDeriv.lean#L8-L36

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_PolyCosSecondDeriv
set_option autoImplicit false
@[expose] public section
public section

theorem PolyCosSecondDeriv (P : Polynomial ℝ) :
    iteratedDeriv 2 (fun t : ℝ => P.eval (Real.cos t)) 0
      = -(Polynomial.derivative P).eval 1 := by sorry
