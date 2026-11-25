-- Prove2me | Theorems.Thm_P2M_GlobalTheory_NormCompat_RatioClose_norm_one_tmul__0e587e6c05b4
-- name    : P2M_GlobalTheory_NormCompat_RatioClose_norm_one_tmul__0e587e6c05b4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:15.233249+00:00
-- url     : https://prove2.me/theorems/4c7784df-61d4-4c62-a42f-54cc142065d7
-- title:
--   P2 M Global Theory Norm Compat Ratio Close norm one tmul  0e587e6c05b4: P2 M Global Theory Norm Compat Ratio Close norm one tmul  0e587e6c05b4
-- statement:
--   The P2 M Global Theory Norm Compat Ratio Close norm one tmul  0e587e6c05b4 construction uses the P2 M Global Theory Norm Compat Ratio Close norm one tmul  0e587e6c05b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormDivLocalEmbeddingCloseToOne.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormDivLocalEmbeddingCloseToOne.lean#L14-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormCloseToOneOfCloseAbovePlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTensorIdempotentOfAlgHomToBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqMulNormIdempotentCornerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationLeOneOfSqSubSelfIntegralBasisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlobalElementNearIdempotentAdicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDivLocalEmbeddingCloseToOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct
open GlobalTheory GlobalTheory.NormCompat GlobalTheory.NormCompat.RatioClose

theorem P2M_GlobalTheory_NormCompat_RatioClose_norm_one_tmul__0e587e6c05b4 {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    [Module.Finite F E] (y : E) :
    Algebra.norm K ((1 : K) ⊗ₜ[F] y) = algebraMap F K (Algebra.norm F y) := by sorry

alias «GlobalTheory».«NormCompat».«RatioClose».«norm_one_tmul'» := P2M_GlobalTheory_NormCompat_RatioClose_norm_one_tmul__0e587e6c05b4
