-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizationIntegerBaseChangeSpecPoint_complexProjection
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizationIntegerBaseChangeSpecPoint_complexProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:34:32.583844+00:00
-- url     : https://prove2.me/theorems/2babfcee-35e7-42a5-a600-a170868aaa88
-- title:
--   Tanner Lifted Product: lps Original Normalization Integer Base Change Spec Point complex Projection
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Normalization Integer Base Change Spec Point complex Projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationComplexPoints.lean#L158-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationComplexPoints.lean#L158-L164

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationOverlapEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationComplexPoints
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffe444fe3b_18
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffe444fe3b_19
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffe444fe3b_24
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffe444fe3b_25
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffe444fe3b_26
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffe444fe3b_27
set_option backward.isDefEq.respectTransparency false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizationIntegerBaseChangeSpecPoint_complexProjection
    (x : LPSOriginalFilledCurve N) :
    lpsOriginalNormalizationIntegerBaseChangeSpecPoint N hpos hN x ≫ pullback.fst _ _ = 𝟙 _ := by sorry
