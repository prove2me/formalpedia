-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_sum_val_inr_a6548b36d2a0
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_sum_val_inr_a6548b36d2a0
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:34.653792+00:00
-- url     : https://prove2.me/theorems/1b4a670d-e596-5c3a-9d28-5a3f01b3a9ae
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart sum val inr a6548b36d2a0: P2 M Ground Theory Heights  Heights Vertical Spec Chart sum val inr a6548b36d2a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart sum val inr a6548b36d2a0 construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart sum val inr a6548b36d2a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L71-L77

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_sum_val_inr_a6548b36d2a0 : ∑ m, val e I j (.inr m) * cx e I j m - 1 = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«sum_val_inr» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_sum_val_inr_a6548b36d2a0
