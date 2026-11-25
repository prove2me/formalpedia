-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_comm_term
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.comm_term
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:58.840019+00:00
-- url     : https://prove2.me/theorems/486536b8-d58b-461a-82f6-713cf0bf0626
-- title:
--   Capelli: comm term
-- statement:
--   The Capelli construction uses the comm term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/RowColA.lean#L115-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/RowColA.lean#L115-L132

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowColA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.comm_term (hE : GlRelR E) {p : ℕ} (R C : Fin (p + 1) → Fin n) (i j : Fin (p + 1)) (y : ℂ) :
    ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
        (E (R i) (C j) * cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) y -
          cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) y * E (R i) (C j)) =
      ∑ t, capT E R C y (i.succAbove t) j - ∑ t, capT E R C y i (j.succAbove t) := by sorry
