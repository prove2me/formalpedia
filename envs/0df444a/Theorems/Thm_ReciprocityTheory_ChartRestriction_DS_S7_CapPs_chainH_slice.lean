-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CapPs_chainH_slice
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CapPs.chainH_slice
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:04:21.643753+00:00
-- url     : https://prove2.me/theorems/99cc79a8-6ad1-5f62-b71b-eaa8e648e8de
-- title:
--   Cap Ps: chain H slice
-- statement:
--   The Cap Ps construction uses the chain H slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ChainHSlice.lean#L84-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ChainHSlice.lean#L84-L95

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ProdOfFnSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ChainHSlice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CapPs
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
local notation "𝕄" => Matrix (Fin n) (Fin n) ℂ
local notation "𝕋" => Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ

theorem ReciprocityTheory.ChartRestriction.DS.S7.CapPs.chainH_slice : ∀ {m : ℕ} (s : Fin m → ℂ × 𝕄) {g : 𝕋 → ℂ}, ContDiffOn ℂ ∞ g (GPs.Wset n) →
    ∀ p ∈ GPs.Wset n, chainH s g p = chainL s (fun y => g (y, p.2)) p.1
  := by sorry
