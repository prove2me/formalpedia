-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_csq_sgE_pp
-- name    : ReciprocityTheory.ChartRestriction.DS.csq_sgE_pp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:54.198585+00:00
-- url     : https://prove2.me/theorems/a3f2f17b-808c-4537-a67f-83c7641b4432
-- title:
--   DS: csq sg E pp
-- statement:
--   The DS construction uses the csq sg E pp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqA.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqA.lean#L51-L56

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqA
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

theorem ReciprocityTheory.ChartRestriction.DS.csq_sgE_pp (ε : Fin n → Bool) (cp cm : Fin n → Fin n → Module.End ℂ W) {a b : Fin n}
    (ha : a ∈ plusIdx ε) (hb : b ∈ plusIdx ε) :
    sgE ε cp cm a b = ∑ x ∈ minusIdx ε, cp a x * cm b x := by sorry
