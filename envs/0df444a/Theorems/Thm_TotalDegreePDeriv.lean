-- Prove2me | Theorems.Thm_TotalDegreePDeriv
-- name    : TotalDegreePDeriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:35:08.290715+00:00
-- url     : https://prove2.me/theorems/a36fcd56-f1e9-4f29-a889-e19193cd7f4f
-- title:
--   Total Degree PDeriv: Total Degree PDeriv
-- statement:
--   Formal partial differentiation drops total degree by at least one. Missing
--   from Mathlib, and the sharp `- 1` is what `TopComponent` needs.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TotalDegreePDeriv.lean#L10-L27
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/TotalDegreePDeriv.lean#L10-L27

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_TotalDegreePDeriv
set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem TotalDegreePDeriv {σ : Type*} (i : σ) (φ : MvPolynomial σ ℝ) :
    (pderiv i φ).totalDegree ≤ φ.totalDegree - 1 := by sorry
