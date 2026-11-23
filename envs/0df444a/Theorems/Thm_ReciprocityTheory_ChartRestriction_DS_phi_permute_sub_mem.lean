-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_phi_permute_sub_mem
-- name    : ReciprocityTheory.ChartRestriction.DS.phi_permute_sub_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:57.10249+00:00
-- url     : https://prove2.me/theorems/699d9ecc-7302-4ece-98e6-e36a735b9559
-- title:
--   DS: phi permute sub mem
-- statement:
--   The DS construction uses the phi permute sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PhiPerm.lean#L104-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PhiPerm.lean#L104-L131

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm
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

theorem ReciprocityTheory.ChartRestriction.DS.phi_permute_sub_mem (hE : IsGlRep E) (hV : IsKStableSub ε E V) {k : ℕ}
    (σ : Equiv.Perm (Fin (k + 1))) {F : Big n (k + 1) M} (hF : F ∈ ncV ε V (k + 1)) :
    phi E (k + 1) F - phi E (k + 1) (permute σ F) ∈ layer ε E V k := by sorry
