-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominantCoweight_eq_zero_of_first_exponent_eq_zero
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominantCoweight_eq_zero_of_first_exponent_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:28:03.942382+00:00
-- url     : https://prove2.me/theorems/e59f4d8e-fe80-4f8f-adde-ae9bb219985d
-- title:
--   Spherical Hecke: projective Dominant Coweight eq zero of first exponent eq zero
-- statement:
--   The Spherical Hecke construction uses the projective Dominant Coweight eq zero of first exponent eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeGenerators.lean#L36-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeGenerators.lean#L36-L46

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Mathlib.Algebra.MvPolynomial.CommRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise Valued
universe u

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominantCoweight_eq_zero_of_first_exponent_eq_zero
    {n : ℕ} (weight : ProjectiveDominantCoweight n)
    (hzero : weight.toDominant.exponent (0 : Fin (n + 1)) = 0) :
    weight = projectiveDominantCoweightZero n := by sorry
