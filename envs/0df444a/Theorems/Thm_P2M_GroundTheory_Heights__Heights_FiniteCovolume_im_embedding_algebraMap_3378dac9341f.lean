-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_im_embedding_algebraMap_3378dac9341f
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_im_embedding_algebraMap_3378dac9341f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:54:40.749707+00:00
-- url     : https://prove2.me/theorems/e5f12038-f456-568c-89a3-7838faaabf89
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume im embedding algebra Map 3378dac9341f: P2 M Ground Theory Heights  Heights Finite Covolume im embedding algebra Map 3378dac9341f
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume im embedding algebra Map 3378dac9341f construction uses the P2 M Ground Theory Heights  Heights Finite Covolume im embedding algebra Map 3378dac9341f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PImaginaryLatticeCocompact.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PImaginaryLatticeCocompact.lean#L13-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StImaginaryLatticeCocompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PImaginaryLatticeCocompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_im_embedding_algebraMap_3378dac9341f (σ : E →+* ℂ) (c : F) : (σ (algebraMap F E c)).im = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«im_embedding_algebraMap» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_im_embedding_algebraMap_3378dac9341f
