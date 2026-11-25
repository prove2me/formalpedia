-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_toBase_mem_b93e47ebd1bd
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_toBase_mem_b93e47ebd1bd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:10.594321+00:00
-- url     : https://prove2.me/theorems/0ae15665-9949-5bba-bc0b-6e42a6a97854
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart mem of to Base mem b93e47ebd1bd: P2 M Ground Theory Heights  Heights Vertical Spec Chart mem of to Base mem b93e47ebd1bd
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart mem of to Base mem b93e47ebd1bd construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart mem of to Base mem b93e47ebd1bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L118-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L118-L125

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_toBase_mem_b93e47ebd1bd [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W)
    {g : MvPolynomial (Fin n) (𝓞 K)} (h : toBase I j g ∈ Wb I j W) : g ∈ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«mem_of_toBase_mem» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_toBase_mem_b93e47ebd1bd
