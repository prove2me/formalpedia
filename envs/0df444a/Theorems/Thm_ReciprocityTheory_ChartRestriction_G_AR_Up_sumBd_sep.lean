-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_sep
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_sep
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:01:07.906842+00:00
-- url     : https://prove2.me/theorems/19796e76-dfdb-4e8e-ac43-1e6446913d2b
-- title:
--   Up: sum Bd sep
-- statement:
--   The Up construction uses the sum Bd sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfB.lean#L48-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfB.lean#L48-L89

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_sep {f : ℕ} (Γ : Subgroup (Fin f → GL (Fin p ⊕ Fin q) ℂ)) (hd : DiscreteTopology Γ)
    (hU : ∀ γ ∈ Γ, ∀ k, IsUpq ((γ k : GL (Fin p ⊕ Fin q) ℂ) :
      Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ γ ∈ Γ, γ ≠ 1 → ∃ k i j,
      c ≤ ‖((γ k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j -
        (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ := by sorry
