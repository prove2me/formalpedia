-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_vogan_min
-- name    : ReciprocityTheory.ChartRestriction.DS.vogan_min
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:04.114015+00:00
-- url     : https://prove2.me/theorems/f9b04e69-b240-4615-8d6b-474f919cf791
-- title:
--   DS: vogan min
-- statement:
--   The DS construction uses the vogan min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/CasimirGapAtNoncompactWeight.lean#L85-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/CasimirGapAtNoncompactWeight.lean#L85-L97

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

theorem ReciprocityTheory.ChartRestriction.DS.vogan_min (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) {μ : Fin n → ℝ} {w : M} (hw : w ∈ genSub E V) (hw0 : w ≠ 0)
    (hμ : IsKHWVec ε E μ w) :
    nsq (lowK ε lam + (2 : ℝ) • rhoC ε) ≤ nsq (μ + (2 : ℝ) • rhoC ε) := by sorry
