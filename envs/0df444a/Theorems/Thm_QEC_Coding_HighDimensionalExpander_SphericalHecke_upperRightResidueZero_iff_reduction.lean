-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_upperRightResidueZero_iff_reduction
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.upperRightResidueZero_iff_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:28.03921+00:00
-- url     : https://prove2.me/theorems/e43b18e0-2a1b-493f-9220-363a09ef1139
-- title:
--   Spherical Hecke: upper Right Residue Zero iff reduction
-- statement:
--   The power-series upper-right residue condition is literally the
--   corresponding zero block after reduction modulo `X`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L403-L409
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L403-L409

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.upperRightResidueZero_iff_reduction
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) :
    UpperRightResidueZero k d r g ↔
      ∀ i j : Fin d, i.val < r → r ≤ j.val →
        powerSeriesReductionGL k d g i j = 0 := by sorry
