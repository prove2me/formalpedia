-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_TraceHermNondegenerate_proof_d7dac07170ad
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_TraceHermNondegenerate_proof_d7dac07170ad
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:17:11.483334+00:00
-- url     : https://prove2.me/theorems/bf7aacff-2f4d-4b9d-b413-78a1b532b58d
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Trace Herm Nondegenerate proof d7dac07170ad: P2 M Ground Theory Heights  Heights Finite Covolume Trace Herm Nondegenerate proof d7dac07170ad
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Trace Herm Nondegenerate proof d7dac07170ad construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Trace Herm Nondegenerate proof d7dac07170ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTraceHermNondegenerate.lean#L20-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTraceHermNondegenerate.lean#L20-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StTraceHermNondegenerate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PTraceHermNondegenerate
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
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_TraceHermNondegenerate_proof_d7dac07170ad (h : HermitianForm F E W) (v : Basis ι E W) :
    TraceHermNondegenerate.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«TraceHermNondegenerate».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_TraceHermNondegenerate_proof_d7dac07170ad
