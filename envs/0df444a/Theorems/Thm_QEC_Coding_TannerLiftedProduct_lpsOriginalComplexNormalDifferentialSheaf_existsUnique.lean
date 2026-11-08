-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalDifferentialSheaf_existsUnique
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalDifferentialSheaf_existsUnique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:55:13.101143+00:00
-- url     : https://prove2.me/theorems/e16af727-7620-4cde-a6ef-3b27e53d6b2a
-- title:
--   Tanner Lifted Product: lps Original Complex Normal Differential Sheaf exists Unique
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Complex Normal Differential Sheaf exists Unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialSheaf.lean#L92-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialSheaf.lean#L92-L100

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialSheaf
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalDifferentialSheaf_existsUnique (M : Scheme.Modules X)
    (d : ((Scheme.Modules.toPresheafOfModules X).obj M).Derivation'
      (schemeConstantPresheafMap X (CommRingCat.of ℂ)
        (lpsOriginalComplexNormalGlobalConstantMap N hpos))) :
    ∃! f : lpsOriginalComplexNormalDifferentialSheaf N hpos ⟶ M,
      (lpsOriginalComplexNormalDifferentialSheafDerivation N hpos).postcomp
        ((Scheme.Modules.toPresheafOfModules X).map f) = d := by sorry
