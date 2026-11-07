-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_neg_one_mem
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0_neg_one_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:21:45.592057+00:00
-- url     : https://prove2.me/theorems/bc149899-4913-4661-8616-6043af48319e
-- title:
--   Tanner Lifted Product: lps Gamma0 neg one mem
-- statement:
--   Minus identity belongs to the actual original Gamma0 group at every level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspWidths.lean#L25-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspWidths.lean#L25-L32

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.Cusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0_neg_one_mem (N : ℕ) : (-1 : GL (Fin 2) ℝ)∈
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := by sorry
