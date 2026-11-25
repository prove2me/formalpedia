-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_WittPartner_proof_a6df1f660009
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_WittPartner_proof_a6df1f660009
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:07:26.181797+00:00
-- url     : https://prove2.me/theorems/8054debd-7cd2-491f-a0dd-ebd4cebf4a35
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Witt Partner proof a6df1f660009: P2 M Ground Theory Heights  Heights Finite Covolume Witt Partner proof a6df1f660009
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Witt Partner proof a6df1f660009 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Witt Partner proof a6df1f660009 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PWittPartner.lean#L12-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PWittPartner.lean#L12-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PWittPartner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_WittPartner_proof_a6df1f660009 (h : HermitianForm F E W) : WittPartner.Statement h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«WittPartner».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_WittPartner_proof_a6df1f660009
