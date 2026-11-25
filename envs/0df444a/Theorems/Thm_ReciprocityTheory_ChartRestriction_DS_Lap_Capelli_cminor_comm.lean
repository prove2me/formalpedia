-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_comm
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:02:25.709681+00:00
-- url     : https://prove2.me/theorems/4aeb7e64-3e5f-401a-b523-140ead2189dc
-- title:
--   Capelli: cminor comm
-- statement:
--   The Capelli construction uses the cminor comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/ProdOfFnUpdateEq.lean#L113-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/ProdOfFnUpdateEq.lean#L113-L150

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq
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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_comm (hE : GlRelR E) (a b : Fin n) {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) :
    E a b * cminor E R C x - cminor E R C x * E a b =
      (∑ t : Fin p, if R t = b then cminor E (Function.update R t a) C x else 0) -
        ∑ t : Fin p, if C t = a then cminor E R (Function.update C t b) x else 0 := by sorry
