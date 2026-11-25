-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isInfUnitary_of_isDerivedOn
-- name    : ReciprocityTheory.ChartRestriction.DS.isInfUnitary_of_isDerivedOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:00.068808+00:00
-- url     : https://prove2.me/theorems/2b6a2cd8-ff0a-408e-8e48-454f93cbef70
-- title:
--   DS: is Inf Unitary of is Derived On
-- statement:
--   The DS construction uses the is Inf Unitary of is Derived On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Unitary.lean#L120-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Unitary.lean#L120-L125

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem ReciprocityTheory.ChartRestriction.DS.isInfUnitary_of_isDerivedOn (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) :
    IsInfUnitary ε E := by sorry
