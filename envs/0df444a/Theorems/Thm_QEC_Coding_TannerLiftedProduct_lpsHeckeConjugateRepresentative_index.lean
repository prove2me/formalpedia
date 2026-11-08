-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateRepresentative_index
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateRepresentative_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:59:31.514244+00:00
-- url     : https://prove2.me/theorems/659d19f4-836f-4705-96d3-7f2282355ce2
-- title:
--   Tanner Lifted Product: lps Hecke Conjugate Representative index
-- statement:
--   The inverse of each true original second representative has its exact zero-based Hecke index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L137-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeEffectiveCovers.lean#L137-L148

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateRepresentative_index (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) :
    lpsHeckeRightIndex N p hNp (lpsHeckeConjugateRepresentative N p hNp i:SL(2,ℤ))⁻¹
      ((CongruenceSubgroup.Gamma0 N).inv_mem
        (lpsHeckeConjugateRepresentative N p hNp i).property)
        (some ⟨0,(Fact.out:p.Prime).pos⟩)=i := by sorry
