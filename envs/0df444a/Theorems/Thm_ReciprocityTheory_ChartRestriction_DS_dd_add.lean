-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dd_add
-- name    : ReciprocityTheory.ChartRestriction.DS.dd_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:51:52.341571+00:00
-- url     : https://prove2.me/theorems/d3ca19aa-1c80-5252-8893-949360430b29
-- title:
--   DS: dd add
-- statement:
--   The DS construction uses the dd add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CsqDdPt.lean#L41-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CsqDdPt.lean#L41-L120

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem ReciprocityTheory.ChartRestriction.DS.dd_add {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) :
    dOp ε E cp * dOp' ε E cm + dOp' ε E cm * dOp ε E cp =
      -(∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, E i a * E a i) + crossT ε E cp cm := by sorry
