-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ValAt_analyticAt_val
-- name    : ReciprocityTheory.ChartRestriction.G.TB.ValAt.analyticAt_val
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:41.792149+00:00
-- url     : https://prove2.me/theorems/721b17d6-ec30-4096-baab-3d6d4f0aa848
-- title:
--   Val At: analytic At val
-- statement:
--   The Val At construction uses the analytic At val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ValAtLem.lean#L77-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ValAtLem.lean#L77-L82

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.ValAt
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X : Scheme.{0}}
open NumberField
variable {g : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.ValAt.analyticAt_val (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (hol : ∀ (U : X.Opens) (f : Γ(X, U)), IsOpen {z | ⊤ ≤ e z ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (e z) U f) {z | ⊤ ≤ e z ⁻¹ᵁ U})
    (U : X.Opens) (f : Γ(X, U)) (z₀ : Fin g → ℂ) (h0 : ⊤ ≤ e z₀ ⁻¹ᵁ U) :
    AnalyticAt ℂ (fun z => valAt' (e z) U f) z₀ := by sorry
