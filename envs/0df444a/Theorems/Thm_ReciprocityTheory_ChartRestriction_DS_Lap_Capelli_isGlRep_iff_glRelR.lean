-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_isGlRep_iff_glRelR
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.isGlRep_iff_glRelR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:42:06.576157+00:00
-- url     : https://prove2.me/theorems/f918af87-6ccd-4e61-8eb9-67cf092bb520
-- title:
--   Capelli: is Gl Rep iff gl Rel R
-- statement:
--   The Capelli construction uses the is Gl Rep iff gl Rel R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/CapelliCentralStatement.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/CapelliCentralStatement.lean#L38-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
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
universe u v w

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.isGlRep_iff_glRelR {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ M) : IsGlRep E ↔ GlRelR E := by sorry
