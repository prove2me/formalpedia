-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_contDiffOn_cplx
-- name    : ReciprocityTheory.AnForm.A.contDiffOn_cplx
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:57.56875+00:00
-- url     : https://prove2.me/theorems/3c35bb09-3bcd-469c-b919-804869456562
-- title:
--   A: cont Diff On cplx
-- statement:
--   The A construction uses the cont Diff On cplx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsIbp.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsIbp.lean#L42-L46

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsIbp
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

theorem ReciprocityTheory.AnForm.A.contDiffOn_cplx {D : ℕ} {a : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)} {n : WithTop ℕ∞}
    (ha : ContDiffOn ℝ n a U) : ContDiffOn ℝ n (cplx a) U := by sorry
