-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_continuous_of_matrix
-- name    : ReciprocityTheory.MultiplicativeHeights.bwp_continuous_of_matrix
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:04:08.240126+00:00
-- url     : https://prove2.me/theorems/cfe766af-fb1f-58ab-bd32-c5b1d0be7cf9
-- title:
--   Multiplicative Heights: bwp continuous of matrix
-- statement:
--   The Multiplicative Heights construction uses the bwp continuous of matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyC.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyC.lean#L68-L72

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

theorem ReciprocityTheory.MultiplicativeHeights.bwp_continuous_of_matrix {p : ℕ} :
    Continuous (fun y : Fin p → Fin p → ℂ => Matrix.of y) := by sorry
