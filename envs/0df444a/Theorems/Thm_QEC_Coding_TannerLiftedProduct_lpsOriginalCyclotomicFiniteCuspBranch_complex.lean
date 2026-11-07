-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicFiniteCuspBranch_complex
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicFiniteCuspBranch_complex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:31:27.630512+00:00
-- url     : https://prove2.me/theorems/14a1a39c-2e73-4edf-be0e-f81fc9eb7cfb
-- title:
--   Tanner Lifted Product: lps Original Cyclotomic Finite Cusp Branch complex
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cyclotomic Finite Cusp Branch complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L115-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L115-L133

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicFiniteCuspBranch_complex (p : ℕ) [Fact p.Prime] (m : ℕ) :
    lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicComplexEmbedding p)
      (lpsOriginalCyclotomicFiniteCuspBranch p m)=
      lpsOriginalAnalyticCuspLocalizedTaylor
        (lpsOriginalAnalyticCuspAffineBranch 1 (by decide) ((m:ℚ)/p)) := by sorry
