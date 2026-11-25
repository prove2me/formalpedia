-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_traceHerm_apply_77d67d8cde12
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_traceHerm_apply_77d67d8cde12
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:59:57.482045+00:00
-- url     : https://prove2.me/theorems/ead32f2f-316d-41f6-809a-875de6b64960
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume trace Herm apply 77d67d8cde12: P2 M Ground Theory Heights  Heights Finite Covolume trace Herm apply 77d67d8cde12
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume trace Herm apply 77d67d8cde12 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume trace Herm apply 77d67d8cde12 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StTraceHermNondegenerate.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StTraceHermNondegenerate.lean#L31-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StTraceHermNondegenerate
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
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_traceHerm_apply_77d67d8cde12 (h : HermitianForm F E W) (v : Basis ι E W) (y z : ι → E) :
    traceHerm h v y z = Algebra.trace ℚ E (h.toSesq (v.equivFun.symm y) (v.equivFun.symm z)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«traceHerm_apply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_traceHerm_apply_77d67d8cde12
