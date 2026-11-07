-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicFormalPrimeProduct_complex
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicFormalPrimeProduct_complex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:32:33.57148+00:00
-- url     : https://prove2.me/theorems/db6dbb40-8b7c-4054-9edd-15cf73549671
-- title:
--   Tanner Lifted Product: lps Original Cyclotomic Formal Prime Product complex
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cyclotomic Formal Prime Product complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L157-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeCuspCorrespondence.lean#L157-L172

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicFormalPrimeProduct_complex (p : ℕ) [Fact p.Prime] :
    (lpsOriginalCyclotomicFormalPrimeProduct p).map
      (lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicComplexEmbedding p))=
      ∏ i : Option (Fin p), (Polynomial.X-Polynomial.C
        (lpsOriginalAnalyticCuspLocalizedTaylor (lpsOriginalAnalyticPrimeBranch p i))) := by sorry
