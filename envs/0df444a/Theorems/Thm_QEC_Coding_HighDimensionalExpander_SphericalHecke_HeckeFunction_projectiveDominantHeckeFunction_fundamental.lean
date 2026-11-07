-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_projectiveDominantHeckeFunction_fundamental
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.projectiveDominantHeckeFunction_fundamental
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:17:34.174131+00:00
-- url     : https://prove2.me/theorems/9b1e6975-633f-4f6e-91b0-9fc3d37932f8
-- title:
--   Hecke Function: projective Dominant Hecke Function fundamental
-- statement:
--   The normalized Cartan family agrees exactly with the previously defined
--   fundamental-color characteristic functions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeAlgebra.lean#L1029-L1037
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeAlgebra.lean#L1029-L1037

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Mathlib.Analysis.Convolution
import Mathlib.LinearAlgebra.Basis.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open MeasureTheory Set Function
open scoped LocalTopology MatrixGroups Pointwise Convolution ComplexConjugate
universe u
open QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.projectiveDominantHeckeFunction_fundamental
    (k : Type u) [Field k] [Finite k] (n r : ℕ) (hr : r ≤ n) :
    projectiveDominantHeckeFunction k
        (fundamentalProjectiveDominantCoweight n r hr) =
      fundamentalHeckeFunction k (n + 1) r := by sorry
