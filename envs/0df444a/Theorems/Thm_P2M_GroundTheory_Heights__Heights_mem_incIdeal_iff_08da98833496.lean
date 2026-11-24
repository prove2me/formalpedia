-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_incIdeal_iff_08da98833496
-- name    : P2M_GroundTheory_Heights__Heights_mem_incIdeal_iff_08da98833496
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:05.66691+00:00
-- url     : https://prove2.me/theorems/7774a52f-b284-45fb-bf89-9fd308fde329
-- title:
--   P2 M Ground Theory Heights  Heights mem inc Ideal iff 08da98833496: P2 M Ground Theory Heights  Heights mem inc Ideal iff 08da98833496
-- statement:
--   The P2 M Ground Theory Heights  Heights mem inc Ideal iff 08da98833496 construction uses the P2 M Ground Theory Heights  Heights mem inc Ideal iff 08da98833496 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChowFormSection.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChowFormSection.lean#L13-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
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
variable {F : Type*} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_mem_incIdeal_iff_08da98833496 {P : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {g : MvPolynomial (Fin k × Fin n) F} :
    g ∈ incIdeal P k ↔ ∀ v ∈ incidence P k, aeval v g = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_incIdeal_iff» := P2M_GroundTheory_Heights__Heights_mem_incIdeal_iff_08da98833496
