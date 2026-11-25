-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_coordEmbed_apply_57a659e1152c
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_coordEmbed_apply_57a659e1152c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:47:59.612978+00:00
-- url     : https://prove2.me/theorems/60707f80-4a20-571a-b4e4-026abe5f2d19
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume coord Embed apply 57a659e1152c: P2 M Ground Theory Heights  Heights Finite Covolume coord Embed apply 57a659e1152c
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume coord Embed apply 57a659e1152c construction uses the P2 M Ground Theory Heights  Heights Finite Covolume coord Embed apply 57a659e1152c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StCoordEmbedBasis.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StCoordEmbedBasis.lean#L18-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StCoordEmbedBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField Module
noncomputable section
variable (E : Type*) [Field E] [NumberField E] (ι : Type*) [Fintype ι]
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_coordEmbed_apply_57a659e1152c (y : ι → E) (w : InfinitePlace E) (i : ι) :
    coordEmbed E ι y w i = w.embedding (y i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«coordEmbed_apply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_coordEmbed_apply_57a659e1152c
