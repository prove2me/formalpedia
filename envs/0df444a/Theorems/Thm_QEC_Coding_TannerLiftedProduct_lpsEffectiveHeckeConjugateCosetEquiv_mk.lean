-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveHeckeConjugateCosetEquiv_mk
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveHeckeConjugateCosetEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:59:16.42264+00:00
-- url     : https://prove2.me/theorems/f11a995e-75c5-4e80-b5ec-b2e70c5a3d61
-- title:
--   Tanner Lifted Product: lps Effective Hecke Conjugate Coset Equiv mk
-- statement:
--   The second effective coset equivalence agrees with original relative coset evaluation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L107-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L107-L122

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveHeckeConjugateCosetEquiv_mk (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (γ : CongruenceSubgroup.Gamma0 N) :
    lpsEffectiveHeckeConjugateCosetEquiv N p hNp
      (QuotientGroup.mk ((MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.subgroupMap
        (CongruenceSubgroup.Gamma0 N) γ)) =
      lpsHeckeConjugateCosetEquiv N p hNp (QuotientGroup.mk γ) := by sorry
