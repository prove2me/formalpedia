-- Prove2me | Theorems.Thm_PositivityTheory_CW_FunctionalCalculusInner_repr_fc
-- name    : PositivityTheory.CW.FunctionalCalculusInner.repr_fc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:51.509694+00:00
-- url     : https://prove2.me/theorems/02590833-9e84-4152-8f15-0741e6ea6267
-- title:
--   Functional Calculus Inner: repr fc
-- statement:
--   The Functional Calculus Inner construction uses the repr fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/FunctionalCalculusOfBasic.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/FunctionalCalculusOfBasic.lean#L18-L27

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

theorem PositivityTheory.CW.FunctionalCalculusInner.repr_fc (b : Module.Basis ι ℂ V) (μ : ι → ℝ) (φ : ℝ → ℝ) (v : V) (i : ι) :
    b.repr (fc b μ φ v) i = ((φ (μ i) : ℝ) : ℂ) * b.repr v i := by sorry
