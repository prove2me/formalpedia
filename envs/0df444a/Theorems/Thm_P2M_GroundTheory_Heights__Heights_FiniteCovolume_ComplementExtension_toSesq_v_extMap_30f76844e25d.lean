-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_toSesq_v_extMap_30f76844e25d
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_toSesq_v_extMap_30f76844e25d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:49:12.606671+00:00
-- url     : https://prove2.me/theorems/ab1f1d39-ec1f-573f-8ad2-5e594c10aa5a
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension to Sesq v ext Map 30f76844e25d: P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension to Sesq v ext Map 30f7
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension to Sesq v ext Map 30f76844e25d construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Extension to Sesq v ext Map 30f76844e25d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementExtension.lean#L71-L76

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_toSesq_v_extMap_30f76844e25d (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    h.toSesq v (extMap hp m x) = h.toSesq v x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementExtension».«toSesq_v_extMap» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_toSesq_v_extMap_30f76844e25d
