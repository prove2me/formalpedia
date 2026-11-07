-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeGamma0CosetDegree
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeGamma0CosetDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:25:51.804336+00:00
-- url     : https://prove2.me/theorems/7c3b3827-688c-485c-9cbc-f5e35f45cc0f
-- title:
--   Tanner Lifted Product: lps Original Prime Gamma0 Coset Degree
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Gamma0 Coset Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L36-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L36-L47

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeGamma0CosetDegree (p : ℕ) [Fact p.Prime] :
    Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)=p+1 := by sorry
