-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GSB_ga_mul_le
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.GSB.ga_mul_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:48:27.057477+00:00
-- url     : https://prove2.me/theorems/464a0030-4993-4c9b-ac09-2ef45e219e86
-- title:
--   GSB: ga mul le
-- statement:
--   The GSB construction uses the ga mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GramReDetLe.lean#L70-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GramReDetLe.lean#L70-L101

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GramReDetLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix InnerProductSpace
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GSB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Xi.GS

theorem ReciprocityTheory.ChartRestriction.DS.Xi.GSB.ga_mul_le (k r : ℕ) (A : Mat k r) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => A *ᵥ Y a) ≤ (gN A ^ 2) ^ (l.val + 1) * Ga k r l Y := by sorry
