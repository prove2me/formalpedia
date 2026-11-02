-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_agm_product_value_scaling
-- name    : QuantumMaxCutEnergy.agm_product_value_scaling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T14:49:20.643347+00:00
-- url     : https://prove2.me/theorems/1c6aeee2-e937-407f-9955-be360837abd2
-- title:
--   Certified SDP-value precision suffices for the 0.953 product-estimation subroutine
-- statement:
--   Let O,W,S,L be real numbers with (O+W)/3≤S, 0.954S≤O, 0≤L≤S and S−L≤W/10000. Then the scaled lower estimate 0.954L is nonnegative, at most O, and at least 0.953(O+W)/3. No division by W occurs, and the case W=0 is included. The theorem is an exact numerical precision conversion: a concrete SDP solver and its running-time proof remain separate.
-- source:
--   Numerical-estimation corollary of Anshu, Gosset and Morenz, TQC2020, Theorem1 and Eqs18–19, https://doi.org/10.4230/LIPIcs.TQC.2020.7 ; rank-three analytic rounding formula in https://doi.org/10.4086/toc.2014.v010a004 . The coefficients 0.954,0.953 and error W/10000 are explicit formalization slack, not a quoted algorithm theorem.

import Mathlib.Data.Real.Basic

theorem QuantumMaxCutEnergy.agm_product_value_scaling (O W S L : ℝ)
    (hstruct : (O + W) / 3 ≤ S)
    (hgap : (0.954 : ℝ) * S ≤ O)
    (hL0 : 0 ≤ L) (hLS : L ≤ S)
    (herror : S - L ≤ W / 10000) :
    0 ≤ (0.954 : ℝ) * L ∧
      (0.954 : ℝ) * L ≤ O ∧
      (0.953 : ℝ) * (O + W) / 3 ≤ (0.954 : ℝ) * L := by sorry
