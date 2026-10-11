-- Prove2me | Theorems.Thm_WeilDefect_RPB108_complex_gram_add_div
-- name    : WeilDefect.RPB108.complex_gram_add_div
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:54:47.104368+00:00
-- url     : https://prove2.me/theorems/b2d3cacb-5289-41c0-9e0e-4befe5c00e1c
-- title:
--   Exact Gram addition and division
-- statement:
--   For real 3×3 matrices V,G, real k and z in ℂ³, define Q_M(z)=Σ_ij M_ij Re(conj(z_i)z_j). Then Q_(V+G/k)(z)=Q_V(z)+Q_G(z)/k. No nonzero or positivity assumption on k is added.
--
--   Exact native statement, definitions and coordinate order are preserved. Original-form realization attachments are unproved future formalization; complete 1.06 positivity, global continuation and RH are not established.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/SchurBounds.lean#L28-L38; exact native theorem WeilDefect.RPB108.complex_gram_add_div. SHA256 559f8c972633086de1625a34c0ae03fa96d241415c6b33e4c028839fb43e7de7. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem WeilDefect.RPB108.complex_gram_add_div (V G : Fin 3 → Fin 3 → ℝ) (k : ℝ) (z : Fin 3 → ℂ) :
    complexGram (fun i j => V i j+G i j/k) z =
      complexGram V z+complexGram G z/k := by sorry
