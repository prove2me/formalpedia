-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_val_free_5c8e5b809709
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_val_free_5c8e5b809709
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:43:26.431082+00:00
-- url     : https://prove2.me/theorems/db5a86a8-4587-489f-adb4-e785fa1c8a57
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart val free 5c8e5b809709: P2 M Ground Theory Heights  Heights Vertical Spec Chart val free 5c8e5b809709
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart val free 5c8e5b809709 construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart val free 5c8e5b809709 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L53-L54

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_val_free_5c8e5b809709 (y : FreePar e j) : val e I j (FreePar.val e j y) = X y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«val_free» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_val_free_5c8e5b809709
