-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_extMap_id_4a8cefbda138
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_extMap_id_4a8cefbda138
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:28:09.037838+00:00
-- url     : https://prove2.me/theorems/1ea0ed8c-3ea5-5572-925d-e1b6e10fa120
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension ext Map id 4a8cefbda138: P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension ext Map id 4a8cefbda138
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension ext Map id 4a8cefbda138 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension ext Map id 4a8cefbda138 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L93-L96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open GroundTheory.Automorphic
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.ComplementExtension
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
variable {h : HermitianForm F E W} {v w : W}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_extMap_id_4a8cefbda138 (hp : IsHyperbolicPair h v w) : extMap hp LinearMap.id = LinearMap.id := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementExtension».«extMap_id» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_extMap_id_4a8cefbda138
