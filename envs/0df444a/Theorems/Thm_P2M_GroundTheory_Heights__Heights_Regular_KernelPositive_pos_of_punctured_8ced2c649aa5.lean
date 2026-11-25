-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_pos_of_punctured_8ced2c649aa5
-- name    : P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_pos_of_punctured_8ced2c649aa5
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:18:50.215315+00:00
-- url     : https://prove2.me/theorems/b5260950-e5d2-4afb-868c-2c396f8835eb
-- title:
--   P2 M Ground Theory Heights  Heights Regular Kernel Positive pos of punctured 8ced2c649aa5: P2 M Ground Theory Heights  Heights Regular Kernel Positive pos of punctured 8ced2c649aa5
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Kernel Positive pos of punctured 8ced2c649aa5 construction uses the P2 M Ground Theory Heights  Heights Regular Kernel Positive pos of punctured 8ced2c649aa5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PKernelPositive.lean#L57-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PKernelPositive.lean#L57-L85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PKernelPositive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.KernelPositive

theorem P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_pos_of_punctured_8ced2c649aa5 {n a g : ℕ} (P : PeriodPolydisc n a g)
    {T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} (hT : P.IsTau0Ext T0) {v : Fin g → ℝ}
    (hv : v ≠ 0) (hB : ∀ i, (P.B i).map (Int.cast : ℤ → ℝ) *ᵥ v = 0) {z : Fin n → ℂ}
    (hz : z ∈ ball (0 : Fin n → ℂ) 1) (hz0 : ∀ k, z k ≠ 0) :
    0 < (cquad v (T0 z)).im := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«KernelPositive».«pos_of_punctured» := P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_pos_of_punctured_8ced2c649aa5
