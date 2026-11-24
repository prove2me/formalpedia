-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_mk_mem_2e2f251b51b3
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_mk_mem_2e2f251b51b3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:10.227072+00:00
-- url     : https://prove2.me/theorems/6303e1ba-347b-484b-8741-4ad15761f912
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart mem of mk mem 2e2f251b51b3: P2 M Ground Theory Heights  Heights Vertical Spec Chart mem of mk mem 2e2f251b51b3
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart mem of mk mem 2e2f251b51b3 construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart mem of mk mem 2e2f251b51b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L93-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L93-L98

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_mk_mem_2e2f251b51b3 [W.IsPrime] (hPW : integralModel I ≤ W) {g : MvPolynomial (Fin n) (𝓞 K)}
    (h : Ideal.Quotient.mk (integralModel I) g ∈ W.map (Ideal.Quotient.mk _)) : g ∈ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«mem_of_mk_mem» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_mem_of_mk_mem_2e2f251b51b3
