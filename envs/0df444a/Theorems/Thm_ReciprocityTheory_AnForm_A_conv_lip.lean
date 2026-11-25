-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_conv_lip
-- name    : ReciprocityTheory.AnForm.A.conv_lip
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:57.650149+00:00
-- url     : https://prove2.me/theorems/361bb43f-e8cb-4fe1-9e49-592bcecdb47e
-- title:
--   A: conv lip
-- statement:
--   The A construction uses the conv lip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollA.lean#L65-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollA.lean#L65-L86

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Convolution
noncomputable section
variable {D : ℕ}
variable (ρ : Mollifier D)

theorem ReciprocityTheory.AnForm.A.conv_lip {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ε : ℝ} (hε : 0 < ε) {g : (Fin D → ℂ) → F} {L : NNReal} (hg : LipschitzWith L g)
    (z : Fin D → ℂ) : ‖(∫ w, ρ.scaled ε w • g (z - w)) - g z‖ ≤ L * ε := by sorry
