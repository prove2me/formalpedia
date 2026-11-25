-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_finite_det_id_line
-- name    : ReciprocityTheory.MultiplicativeHeights.bwp_finite_det_id_line
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:07.851572+00:00
-- url     : https://prove2.me/theorems/123f5bc4-f5d3-4835-a8fd-4f7d21a11322
-- title:
--   Multiplicative Heights: bwp finite det id line
-- statement:
--   The Multiplicative Heights construction uses the bwp finite det id line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyC.lean#L54-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyC.lean#L54-L66

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyA
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Polynomial

theorem ReciprocityTheory.MultiplicativeHeights.bwp_finite_det_id_line {p : ℕ} (z : Fin p × Fin p → ℂ) :
    {s : ℂ | (bwpMat (z + s • bwpId p)).det = 0}.Finite := by sorry
