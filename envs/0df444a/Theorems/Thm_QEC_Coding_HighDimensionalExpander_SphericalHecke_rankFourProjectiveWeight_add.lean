-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourProjectiveWeight_add
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourProjectiveWeight_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:28:01.702215+00:00
-- url     : https://prove2.me/theorems/02039dd7-8928-459f-80ad-759cd7351da8
-- title:
--   Spherical Hecke: rank Four Projective Weight add
-- statement:
--   The Spherical Hecke construction uses the rank Four Projective Weight add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeGenerators.lean#L1059-L1066
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeGenerators.lean#L1059-L1066

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Mathlib.Algebra.MvPolynomial.CommRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise Valued
universe u

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourProjectiveWeight_add (a b : Fin 3 → ℕ) :
    rankFourProjectiveWeight (a + b) =
      projectiveDominantCoweightAdd
        (rankFourProjectiveWeight a) (rankFourProjectiveWeight b) := by sorry
