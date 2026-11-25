-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefD_comb
-- name    : ReciprocityTheory.ChartRestriction.DS.coefD_comb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:20.630421+00:00
-- url     : https://prove2.me/theorems/7c8e68ed-e036-439b-9bc2-a1ba47048efd
-- title:
--   DS: coef D comb
-- statement:
--   The DS construction uses the coef D comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefDTensActPow.lean#L115-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefDTensActPow.lean#L115-L127

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefCExpEntrySummable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefDTensActPow
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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem ReciprocityTheory.ChartRestriction.DS.coefD_comb (s : ℂ) (m : ℕ) (B : Matrix (Fin n) (Fin n) ℂ) (L : Fin n → Fin n → ℕ → ℂ) :
    s ^ m / (m.factorial : ℂ) * ∑ c, ∑ kl ∈ antidiagonal m, (m.choose kl.1 : ℂ) *
        ∑ d, (B ^ kl.1) c d * L c d kl.2 =
      ∑ c, ∑ d, ∑ kl ∈ antidiagonal m,
        s ^ kl.1 / (kl.1.factorial : ℂ) * (B ^ kl.1) c d * (s ^ kl.2 / (kl.2.factorial : ℂ) * L c d kl.2) := by sorry
