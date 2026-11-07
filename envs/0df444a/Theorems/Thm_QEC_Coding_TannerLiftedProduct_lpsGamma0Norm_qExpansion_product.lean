-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Norm_qExpansion_product
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0Norm_qExpansion_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:20:47.764893+00:00
-- url     : https://prove2.me/theorems/f14464d5-6bfe-48ea-afb7-cf2649fee92a
-- title:
--   Tanner Lifted Product: lps Gamma0 Norm q Expansion product
-- statement:
--   The actual modular-form norm expansion is the finite product of the quotient expansions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceSturm.lean#L95-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceSturm.lean#L95-L107

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFourierPeriodChange
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0Norm_qExpansion_product (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    UpperHalfPlane.qExpansion (N:ℝ) (ModularForm.norm 𝒮ℒ f)=
      let : Fintype (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :=
        Fintype.ofFinite _
      ∏ q : 𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ,
        UpperHalfPlane.qExpansion (N:ℝ) (SlashInvariantForm.quotientFunc f q) := by sorry
