-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_finite_det_line
-- name    : ReciprocityTheory.MultiplicativeHeights.bwp_finite_det_line
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:54.255442+00:00
-- url     : https://prove2.me/theorems/dbbf0c8d-8d75-4145-8238-f265c074164e
-- title:
--   Multiplicative Heights: bwp finite det line
-- statement:
--   The Multiplicative Heights construction uses the bwp finite det line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyC.lean#L40-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyC.lean#L40-L52

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

theorem ReciprocityTheory.MultiplicativeHeights.bwp_finite_det_line {p : ℕ} (z v : Fin p × Fin p → ℂ) (hz : (bwpMat z).det ≠ 0) :
    {t : ℂ | (bwpMat (z + t • v)).det = 0}.Finite := by sorry
