-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_inK_apply_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.inK_apply_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:38.359032+00:00
-- url     : https://prove2.me/theorems/69f84fd6-51be-4432-8df3-0d2772f77227
-- title:
--   DS: in K apply eq zero
-- statement:
--   The DS construction uses the in K apply eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/ConjTransposeEqOfInG.lean#L78-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/ConjTransposeEqOfInG.lean#L78-L85

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InPApplyEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
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
open scoped Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.inK_apply_eq_zero {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z)
    {a b : Fin n} (hab : ε a ≠ ε b) : Z a b = 0 := by sorry
