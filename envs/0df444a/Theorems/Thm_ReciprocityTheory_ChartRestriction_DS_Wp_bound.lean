-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Wp_bound
-- name    : ReciprocityTheory.ChartRestriction.DS.Wp_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:08:21.564802+00:00
-- url     : https://prove2.me/theorems/1d659798-0dc2-40d8-ba90-119d22eaeb68
-- title:
--   DS: Wp bound
-- statement:
--   The DS construction uses the Wp bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/NcVOneDecomp.lean#L91-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/NcVOneDecomp.lean#L91-L144

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CrossOpEigGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
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

theorem ReciprocityTheory.ChartRestriction.DS.Wp_bound (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {x : Big n 1 M} (hx : x ∈ Wp ε E V) :
    2 * (h - n + 1) * ‖x‖ ^ 2 ≤ 2 * RCLike.re (inner ℂ (crossOp ε E 1 0 x) x) := by sorry
