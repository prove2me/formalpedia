-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_khw_lowK_mem
-- name    : ReciprocityTheory.ChartRestriction.DS.khw_lowK_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:19:29.989879+00:00
-- url     : https://prove2.me/theorems/32d1e8dd-79ce-4a40-a216-51af6ed5a93a
-- title:
--   DS: khw low K mem
-- statement:
--   The DS construction uses the khw low K mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/CasimirGapAtNoncompactWeight.lean#L60-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/CasimirGapAtNoncompactWeight.lean#L60-L73

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
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
  {E : Fin n → Fin n → Module.End ℂ M} {lam : Fin n → ℝ} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.khw_lowK_mem (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) {w : M} (hw : w ∈ genSub E V) (hμ : IsKHWVec ε E (lowK ε lam) w) :
    w ∈ V := by sorry
