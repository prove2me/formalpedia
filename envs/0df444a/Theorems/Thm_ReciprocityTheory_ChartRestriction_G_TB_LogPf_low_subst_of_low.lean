-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_low_subst_of_low
-- name    : ReciprocityTheory.ChartRestriction.G.TB.LogPf.low_subst_of_low
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:49.394192+00:00
-- url     : https://prove2.me/theorems/bb36effa-187d-5d0f-899a-a72c71c41276
-- title:
--   Log Pf: low subst of low
-- statement:
--   The Log Pf construction uses the low subst of low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LogChain.lean#L64-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LogChain.lean#L64-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries Formalism.FG.SolveVAux
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {σ τ : Type}

theorem ReciprocityTheory.ChartRestriction.G.TB.LogPf.low_subst_of_low [Finite σ] {a : σ → MvPowerSeries τ k} (ha : ∀ s, Low 1 (a s)) {N : ℕ}
    {g : MvPowerSeries σ k} (hg : Low N g) : Low N (subst a g) := by sorry
