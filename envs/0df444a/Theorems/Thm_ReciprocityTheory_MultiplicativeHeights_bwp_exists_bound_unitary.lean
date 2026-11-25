-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_exists_bound_unitary
-- name    : ReciprocityTheory.MultiplicativeHeights.bwp_exists_bound_unitary
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:04:12.114585+00:00
-- url     : https://prove2.me/theorems/64396933-717a-4605-bfc6-a241c7010f8b
-- title:
--   Multiplicative Heights: bwp exists bound unitary
-- statement:
--   The Multiplicative Heights construction uses the bwp exists bound unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyC.lean#L74-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyC.lean#L74-L103

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

theorem ReciprocityTheory.MultiplicativeHeights.bwp_exists_bound_unitary {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ → ℂ) (hP : IsHoloGL P) :
    ∃ C : ℝ, ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ‖P U‖ ≤ C := by sorry
