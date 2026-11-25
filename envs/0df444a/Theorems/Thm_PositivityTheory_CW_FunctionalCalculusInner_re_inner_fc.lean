-- Prove2me | Theorems.Thm_PositivityTheory_CW_FunctionalCalculusInner_re_inner_fc
-- name    : PositivityTheory.CW.FunctionalCalculusInner.re_inner_fc
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:50:23.029188+00:00
-- url     : https://prove2.me/theorems/1a67d97b-65dc-5e49-a8d9-94daa3713784
-- title:
--   Functional Calculus Inner: re inner fc
-- statement:
--   The Functional Calculus Inner construction uses the re inner fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/FunctionalCalculusOfBasic.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/FunctionalCalculusOfBasic.lean#L62-L66

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusOfBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.FunctionalCalculusInner
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}

theorem PositivityTheory.CW.FunctionalCalculusInner.re_inner_fc (b : Module.Basis ι ℂ V) (hb : Orthonormal ℂ b) (μ : ι → ℝ) (φ : ℝ → ℝ) (w : V) :
    (inner ℂ w (fc b μ φ w)).re = ∑ i ∈ (b.repr w).support, φ (μ i) * ‖b.repr w i‖ ^ 2 := by sorry
