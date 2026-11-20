-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussFrickeOrderMap_generatedDiagram
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussFrickeOrderMap_generatedDiagram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:16:27.742307+00:00
-- url     : https://prove2.me/theorems/5816691f-b8bb-4eae-819d-da521d8c5d9d
-- title:
--   Tanner Lifted Product: lps Original Gauss Fricke Order Map generated Diagram
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Fricke Order Map generated Diagram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFricke.lean#L179-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFricke.lean#L179-L214

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFricke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussFrickeOrderMap_generatedDiagram
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGaussAffineToGenerated N hN p).comp
      (lpsOriginalGaussFrickeOrderMap N hN p hpN) =
        (lpsOriginalRationalFrickePullback N hN).comp
          (lpsOriginalGaussAffineToGenerated N hN p) := by sorry
