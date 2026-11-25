-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_finrank_eig_bc
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.finrank_eig_bc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:57.950215+00:00
-- url     : https://prove2.me/theorems/6dfb8e66-19d6-4805-b997-cda8c31e910a
-- title:
--   Chart: finrank eig bc
-- statement:
--   The Chart construction uses the finrank eig bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankLin.lean#L62-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankLin.lean#L62-L147

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open Module
variable {V k : Type} [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field k] [Algebra V k] [FaithfulSMul V k]

theorem ReciprocityTheory.ChartRestriction.G.Chart.finrank_eig_bc {n : ℕ} {O : Type} (L : O → (Fin n → V) →ₗ[V] (Fin n → V))
    (Lk : O → (Fin n → k) →ₗ[k] (Fin n → k)) (hL : ∀ a c, Lk a (algebraMap V k ∘ c) = algebraMap V k ∘ L a c)
    (χ : O → V) :
    finrank V (⨅ a, LinearMap.ker (L a - χ a • LinearMap.id) : Submodule V (Fin n → V)) =
      finrank k (⨅ a, LinearMap.ker (Lk a - algebraMap V k (χ a) • LinearMap.id) : Submodule k (Fin n → k)) := by sorry
