-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_powerset_map_emb_74d7138d59bc
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_powerset_map_emb_74d7138d59bc
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:06:29.419797+00:00
-- url     : https://prove2.me/theorems/a539747b-2893-52c0-ae43-ff2ed110ca44
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman powerset map emb 74d7138d59bc: P2 M Ground Theory Heights  Heights Kleiman powerset map emb 74d7138d59bc
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman powerset map emb 74d7138d59bc construction uses the P2 M Ground Theory Heights  Heights Kleiman powerset map emb 74d7138d59bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumAdditive.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumAdditive.lean#L62-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumAdditive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumEventual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterSumTopVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_InterSumEventuallyEqInterNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumAdditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_powerset_map_emb_74d7138d59bc {α β : Type*} (e : α ↪ β) (s : Finset α) :
    (s.map e).powerset = s.powerset.map (Finset.mapEmbedding e).toEmbedding := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«powerset_map_emb» := P2M_GroundTheory_Heights__Heights_Kleiman_powerset_map_emb_74d7138d59bc
