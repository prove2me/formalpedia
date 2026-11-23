-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Wm_kStable
-- name    : ReciprocityTheory.ChartRestriction.DS.Wm_kStable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:57.676937+00:00
-- url     : https://prove2.me/theorems/0692657a-32dd-4526-ad8d-6ca7a22e4adc
-- title:
--   DS: Wm k Stable
-- statement:
--   The DS construction uses the Wm k Stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/InnerCrossOpEigEqZero.lean#L128-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/InnerCrossOpEigEqZero.lean#L128-L144

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Weights
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_InnerCrossOpEigEqZero
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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem ReciprocityTheory.ChartRestriction.DS.Wm_kStable (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) : IsKStableSub ε (bAct E 1) (Wm ε E V) := by sorry
