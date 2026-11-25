-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_diagE_compact
-- name    : ReciprocityTheory.ChartRestriction.DS.diagE_compact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:11.472062+00:00
-- url     : https://prove2.me/theorems/3410ba8d-1136-4aa4-953f-9629fddea9ca
-- title:
--   DS: diag E compact
-- statement:
--   The DS construction uses the diag E compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean#L227-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean#L227-L238

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
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
variable {n : ℕ}
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem ReciprocityTheory.ChartRestriction.DS.diagE_compact {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b : Fin n) (h : ε a = ε b) :
    diagE ε E cp cm a b * diagE ε E cp cm b a - diagE ε E cp cm b a * diagE ε E cp cm a b =
      diagE ε E cp cm a a - diagE ε E cp cm b b := by sorry
