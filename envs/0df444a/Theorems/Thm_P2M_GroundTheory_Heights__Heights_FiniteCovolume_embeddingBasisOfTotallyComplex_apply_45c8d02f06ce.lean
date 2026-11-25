-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_embeddingBasisOfTotallyComplex_apply_45c8d02f06ce
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_embeddingBasisOfTotallyComplex_apply_45c8d02f06ce
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:41:17.631613+00:00
-- url     : https://prove2.me/theorems/c61ce26a-ae93-4742-8c82-79a97173df97
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume embedding Basis Of Totally Complex apply 45c8d02f06ce: P2 M Ground Theory Heights  Heights Finite Covolume embedding Basis Of Totally Complex apply
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume embedding Basis Of Totally Complex apply 45c8d02f06ce construction uses the P2 M Ground Theory Heights  Heights Finite Covolume embedding Basis Of Totally Complex apply 45c8d02f06ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PCoordEmbedBasis.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PCoordEmbedBasis.lean#L29-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StCoordEmbedBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCoordEmbedBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField Module NumberField.InfinitePlace NumberField.mixedEmbedding
noncomputable section
variable (E : Type*) [Field E] [NumberField E] (ι : Type*) [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_embeddingBasisOfTotallyComplex_apply_45c8d02f06ce [IsTotallyComplex E]
    (j : Free.ChooseBasisIndex ℤ (𝓞 E)) (w : InfinitePlace E) :
    embeddingBasisOfTotallyComplex E j w = w.embedding (integralBasis E j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«embeddingBasisOfTotallyComplex_apply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_embeddingBasisOfTotallyComplex_apply_45c8d02f06ce
