-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_st_gradDens_leibniz
-- name    : ReciprocityTheory.AnForm.M.st_gradDens_leibniz
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:51:43.570797+00:00
-- url     : https://prove2.me/theorems/e397c210-502c-4227-8b82-5dc99f4774b1
-- title:
--   M: st grad Dens leibniz
-- statement:
--   The M construction uses the st grad Dens leibniz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesD.lean#L37-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesD.lean#L37-L74

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.M.st_gradDens_leibniz {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    (a b c : (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) (ha : DifferentiableAt ℝ a y)
    (hb : DifferentiableAt ℝ b y) (hc : c =ᶠ[𝓝 y] fun z => a z * b z) :
    gradDens φ c b y = a y * gradDens φ b b y + gradDens φ a (fun z => 1 / 2 * (b z * b z)) y := by sorry
