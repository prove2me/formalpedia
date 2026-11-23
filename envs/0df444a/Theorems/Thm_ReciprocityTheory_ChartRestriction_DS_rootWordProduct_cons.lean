-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rootWordProduct_cons
-- name    : ReciprocityTheory.ChartRestriction.DS.rootWordProduct_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:43:35.398549+00:00
-- url     : https://prove2.me/theorems/2e3d1168-317c-4d4c-ac55-89868be3f0f1
-- title:
--   DS: root Word Product cons
-- statement:
--   The DS construction uses the root Word Product cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L52-L56

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
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
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.rootWordProduct_cons {k : ℕ} (p : Fin n × Fin n) (κ : Fin k → Fin n × Fin n) :
    word E (Fin.cons p κ : Fin (k + 1) → Fin n × Fin n) = E p.1 p.2 * word E κ := by sorry
