-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_low_pderiv
-- name    : ReciprocityTheory.ChartRestriction.G.TB.LogPf.low_pderiv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:49.3219+00:00
-- url     : https://prove2.me/theorems/5b93901c-bc32-5247-9265-b4ed6bb38e31
-- title:
--   Log Pf: low pderiv
-- statement:
--   The Log Pf construction uses the low pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LogChain.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LogChain.lean#L14-L22

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

theorem ReciprocityTheory.ChartRestriction.G.TB.LogPf.low_pderiv {N : ℕ} {g : MvPowerSeries τ k} (hg : Low (N + 1) g) (t : τ) : Low N (pderiv k t g) := by sorry
