-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_span_X_zero_mem_relComps_0c705e008944
-- name    : P2M_GroundTheory_Heights__Heights_span_X_zero_mem_relComps_0c705e008944
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:17.768991+00:00
-- url     : https://prove2.me/theorems/d55c49f6-5fdd-4bed-9e34-2a60ea289f89
-- title:
--   P2 M Ground Theory Heights  Heights span X zero mem rel Comps 0c705e008944: P2 M Ground Theory Heights  Heights span X zero mem rel Comps 0c705e008944
-- statement:
--   The P2 M Ground Theory Heights  Heights span X zero mem rel Comps 0c705e008944 construction uses the P2 M Ground Theory Heights  Heights span X zero mem rel Comps 0c705e008944 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/Statements.lean#L142-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/Statements.lean#L142-L154

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_span_X_zero_mem_relComps_0c705e008944 (F : Type*) [Field F] :
    Ideal.span {X 0} ∈ relComps ((⊥ : Ideal (MvPolynomial (Fin 2) F)) ⊔
      Ideal.span {linForm (fun j : Fin 2 => if j = 0 then (1 : F) else 0)}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«span_X_zero_mem_relComps» := P2M_GroundTheory_Heights__Heights_span_X_zero_mem_relComps_0c705e008944
