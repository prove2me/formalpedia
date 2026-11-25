-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_sndDeriv_I_I
-- name    : ReciprocityTheory.AnForm.sndDeriv_I_I
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:29.115182+00:00
-- url     : https://prove2.me/theorems/e173924e-ab69-431b-8ea4-990195b92655
-- title:
--   An Form: snd Deriv I I
-- statement:
--   The An Form construction uses the snd Deriv I I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PshShiftA.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PshShiftA.lean#L34-L36

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Filter Topology
open scoped ContDiff
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem ReciprocityTheory.AnForm.sndDeriv_I_I {τ : (ι → ℂ) → (κ → ℂ)} {z : ι → ℂ} (hτ : AnalyticAt ℂ τ z) (a : ι → ℂ) :
    fderiv ℝ (fderiv ℝ τ) z (Complex.I • a) (Complex.I • a) = - fderiv ℝ (fderiv ℝ τ) z a a := by sorry
