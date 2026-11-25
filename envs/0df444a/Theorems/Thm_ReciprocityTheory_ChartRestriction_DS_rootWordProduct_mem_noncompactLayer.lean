-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rootWordProduct_mem_noncompactLayer
-- name    : ReciprocityTheory.ChartRestriction.DS.rootWordProduct_mem_noncompactLayer
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:53:23.381885+00:00
-- url     : https://prove2.me/theorems/fca3c2c8-1f24-4ddb-ad27-241e6e4a12d6
-- title:
--   DS: root Word Product mem noncompact Layer
-- statement:
--   The DS construction uses the root Word Product mem noncompact Layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L162-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L162-L172

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

theorem ReciprocityTheory.ChartRestriction.DS.rootWordProduct_mem_noncompactLayer : ∀ {k : ℕ} (κ : Fin k → Fin n × Fin n),
    (∀ i, ε (κ i).1 ≠ ε (κ i).2) → ∀ v ∈ V, word E κ v ∈ layer ε E V k
  := by sorry
