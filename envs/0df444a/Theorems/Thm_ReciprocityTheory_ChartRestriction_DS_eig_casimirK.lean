-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_eig_casimirK
-- name    : ReciprocityTheory.ChartRestriction.DS.eig_casimirK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:39.46927+00:00
-- url     : https://prove2.me/theorems/9fbcbb2d-5c3f-423c-98a9-1089f57ed184
-- title:
--   DS: eig casimir K
-- statement:
--   The DS construction uses the eig casimir K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/KUnitB.lean#L80-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/KUnitB.lean#L80-L110

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
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
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}

theorem ReciprocityTheory.ChartRestriction.DS.eig_casimirK (hA : IsGlRep A) (hU : IsKUnitary ε A) {S : Submodule ℂ X}
    (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) {x : X} (hx : x ∈ S) (hx0 : x ≠ 0)
    {θ : ℂ} (hθ : casimirK ε A x = θ • x) :
    ∃ w ∈ S, w ≠ 0 ∧ casimirK ε A w = θ • w ∧ ∃ μ : Fin n → ℝ, IsKHWVec ε A μ w ∧
      θ = (casValK ε μ : ℂ) := by sorry
