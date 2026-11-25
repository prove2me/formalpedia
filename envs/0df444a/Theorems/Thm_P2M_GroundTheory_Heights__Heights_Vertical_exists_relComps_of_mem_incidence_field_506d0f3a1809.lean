-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_exists_relComps_of_mem_incidence_field_506d0f3a1809
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_exists_relComps_of_mem_incidence_field_506d0f3a1809
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:43:09.685817+00:00
-- url     : https://prove2.me/theorems/819a3d12-b48b-4c18-b014-b4c62938aec1
-- title:
--   P2 M Ground Theory Heights  Heights Vertical exists rel Comps of mem incidence field 506d0f3a1809: P2 M Ground Theory Heights  Heights Vertical exists rel Comps of mem incidence field 506d0f3a1809
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical exists rel Comps of mem incidence field 506d0f3a1809 construction uses the P2 M Ground Theory Heights  Heights Vertical exists rel Comps of mem incidence field 506d0f3a1809 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecFirstNeField.lean#L13-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecFirstNeField.lean#L13-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSpecFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecFirstNeField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Vertical_exists_relComps_of_mem_incidence_field_506d0f3a1809 {F : Type*} [Field F] {n k : ℕ}
    {J : Ideal (MvPolynomial (Fin n) F)} {v : Fin k × Fin n → AlgebraicClosure F}
    (hv : v ∈ incidence J k) : ∃ W ∈ relComps J, v ∈ incidence W k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«exists_relComps_of_mem_incidence_field» := P2M_GroundTheory_Heights__Heights_Vertical_exists_relComps_of_mem_incidence_field_506d0f3a1809
