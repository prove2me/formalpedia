-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_C_toBase_mem_Q_0755be110dc4
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_C_toBase_mem_Q_0755be110dc4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:43:24.845646+00:00
-- url     : https://prove2.me/theorems/d2c07c3b-aebd-4936-9789-41ec8e59c4d1
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart C to Base mem Q 0755be110dc4: P2 M Ground Theory Heights  Heights Vertical Spec Chart C to Base mem Q 0755be110dc4
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart C to Base mem Q 0755be110dc4 construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart C to Base mem Q 0755be110dc4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L131-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L131-L133

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
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
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Vertical.SpecChart
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
  (j : Fin n)
variable (W : Ideal (MvPolynomial (Fin n) (𝓞 K)))
variable {I W}

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_C_toBase_mem_Q_0755be110dc4 {g : MvPolynomial (Fin n) (𝓞 K)} (hg : g ∈ W) : C (toBase I j g) ∈ Q e I j W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«C_toBase_mem_Q» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_C_toBase_mem_Q_0755be110dc4
