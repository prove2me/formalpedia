-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominantCoweightAdd_comm
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominantCoweightAdd_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:27:47.252016+00:00
-- url     : https://prove2.me/theorems/9b755cad-e63c-452a-8c92-657e2f805d87
-- title:
--   Spherical Hecke: projective Dominant Coweight Add comm
-- statement:
--   The Spherical Hecke construction uses the projective Dominant Coweight Add comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeGenerators.lean#L97-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeGenerators.lean#L97-L102

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Mathlib.Algebra.MvPolynomial.CommRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise Valued
universe u

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominantCoweightAdd_comm {n : ℕ}
    (a b : ProjectiveDominantCoweight n) :
    projectiveDominantCoweightAdd a b = projectiveDominantCoweightAdd b a := by sorry
