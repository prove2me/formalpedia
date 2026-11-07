-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeProjectiveWeight_add
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeProjectiveWeight_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:27:37.31569+00:00
-- url     : https://prove2.me/theorems/bfb65a2b-87d9-4a37-a805-da5ca0cea6da
-- title:
--   Spherical Hecke: rank Three Projective Weight add
-- statement:
--   The Spherical Hecke construction uses the rank Three Projective Weight add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeGenerators.lean#L982-L990
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeGenerators.lean#L982-L990

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Mathlib.Algebra.MvPolynomial.CommRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise Valued
universe u

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeProjectiveWeight_add (a b : Fin 2 → ℕ) :
    rankThreeProjectiveWeight (a + b) =
      projectiveDominantCoweightAdd
        (rankThreeProjectiveWeight a) (rankThreeProjectiveWeight b) := by sorry
