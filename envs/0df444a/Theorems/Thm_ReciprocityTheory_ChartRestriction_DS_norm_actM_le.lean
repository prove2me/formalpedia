-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_norm_actM_le
-- name    : ReciprocityTheory.ChartRestriction.DS.norm_actM_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:53:37.692057+00:00
-- url     : https://prove2.me/theorems/be3868a8-2334-48b0-bc0b-4cf404d16d95
-- title:
--   DS: norm act M le
-- statement:
--   The DS construction uses the norm act M le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Growth.lean#L35-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Growth.lean#L35-L82

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Growth
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

theorem ReciprocityTheory.ChartRestriction.DS.norm_actM_le {R d : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 ≤ ((R + √2 * k) ^ 2 - d) * ‖x‖ ^ 2)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (k : ℕ) {x : M} (hx : x ∈ layer ε E V k) :
    ‖actM E X x‖ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * (R + √(max 0 (-d)) + √2 * k) * ‖x‖ := by sorry
