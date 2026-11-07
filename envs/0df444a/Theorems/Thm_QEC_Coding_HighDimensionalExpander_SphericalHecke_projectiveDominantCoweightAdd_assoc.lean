-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominantCoweightAdd_assoc
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominantCoweightAdd_assoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:27:42.033912+00:00
-- url     : https://prove2.me/theorems/4de65f56-6549-482e-9fec-9b0e0e4c2a84
-- title:
--   Spherical Hecke: projective Dominant Coweight Add assoc
-- statement:
--   The Spherical Hecke construction uses the projective Dominant Coweight Add assoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeGenerators.lean#L89-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeGenerators.lean#L89-L95

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Mathlib.Algebra.MvPolynomial.CommRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise Valued
universe u

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominantCoweightAdd_assoc {n : ℕ}
    (a b c : ProjectiveDominantCoweight n) :
    projectiveDominantCoweightAdd (projectiveDominantCoweightAdd a b) c =
      projectiveDominantCoweightAdd a (projectiveDominantCoweightAdd b c) := by sorry
