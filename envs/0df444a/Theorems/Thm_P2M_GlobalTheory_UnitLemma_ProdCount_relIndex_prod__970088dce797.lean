-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitLemma_ProdCount_relIndex_prod__970088dce797
-- name    : P2M_GlobalTheory_UnitLemma_ProdCount_relIndex_prod__970088dce797
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:10:54.127953+00:00
-- url     : https://prove2.me/theorems/4e39832a-e098-4aca-8368-c6223b0efb80
-- title:
--   P2 M Global Theory Unit Lemma Prod Count rel Index prod  970088dce797: P2 M Global Theory Unit Lemma Prod Count rel Index prod  970088dce797
-- statement:
--   The P2 M Global Theory Unit Lemma Prod Count rel Index prod  970088dce797 construction uses the P2 M Global Theory Unit Lemma Prod Count rel Index prod  970088dce797 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L36-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountProdOfIdempotentSeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.ProdCount
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial

theorem P2M_GlobalTheory_UnitLemma_ProdCount_relIndex_prod__970088dce797 {A B : Type} [Group A] [Group B] (H₁ K₁ : Subgroup A) (H₂ K₂ : Subgroup B) :
    (H₁.prod H₂).relIndex (K₁.prod K₂) = H₁.relIndex K₁ * H₂.relIndex K₂ := by sorry

alias «GlobalTheory».«UnitLemma».«ProdCount».«relIndex_prod'» := P2M_GlobalTheory_UnitLemma_ProdCount_relIndex_prod__970088dce797
