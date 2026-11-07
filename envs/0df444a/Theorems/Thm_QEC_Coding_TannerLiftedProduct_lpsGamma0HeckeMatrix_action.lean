-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0HeckeMatrix_action
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0HeckeMatrix_action
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:52:10.790011+00:00
-- url     : https://prove2.me/theorems/6caeb798-835f-47bd-88a0-f24d20e3484b
-- title:
--   Tanner Lifted Product: lps Gamma0 Hecke Matrix action
-- statement:
--   The genuine Hecke matrix acts on coordinates exactly as the actual cusp endomorphism.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceFiniteDimension.lean#L98-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceFiniteDimension.lean#L98-L103

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0HeckeMatrix_action (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    (lpsGamma0HeckeMatrix N p hNp).mulVec ((lpsGamma0CuspBasis N 2).repr f) =
      (lpsGamma0CuspBasis N 2).repr (lpsCuspHeckeLinearMap N p hNp f) := by sorry
