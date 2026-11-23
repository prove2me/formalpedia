-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_cons_eq
-- name    : ReciprocityTheory.AnForm.A.maDens_cons_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:52.542687+00:00
-- url     : https://prove2.me/theorems/bbf61afd-b0da-4e8a-91a6-ee9b2ea61083
-- title:
--   A: ma Dens cons eq
-- statement:
--   The A construction uses the ma Dens cons eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsPiola.lean#L357-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsPiola.lean#L357-L365

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section

theorem ReciprocityTheory.AnForm.A.maDens_cons_eq {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v : (Fin (n + 1) → ℂ) → ℝ)
    (z : Fin (n + 1) → ℂ) :
    maDens (Fin.cons v φ) z = ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
      (mdisc (Fin.cons (hessC v z) fun i => hessC (φ i) z)).re := by sorry
