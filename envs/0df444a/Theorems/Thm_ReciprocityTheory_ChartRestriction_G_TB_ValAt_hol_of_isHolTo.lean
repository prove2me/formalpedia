-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ValAt_hol_of_isHolTo
-- name    : ReciprocityTheory.ChartRestriction.G.TB.ValAt.hol_of_isHolTo
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:38.714234+00:00
-- url     : https://prove2.me/theorems/7e79764c-9043-4936-a761-41e9b4d57f1f
-- title:
--   Val At: hol of is Hol To
-- statement:
--   The Val At construction uses the hol of is Hol To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ValAtLem.lean#L84-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ValAtLem.lean#L84-L99

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

theorem ReciprocityTheory.ChartRestriction.G.TB.ValAt.hol_of_isHolTo (F : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (h : IsHolTo ((Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ)))
      (fun bz : (Fin 0 → ℂ) × (Fin g → ℂ) => F bz.2)) (U : X.Opens) (f : Γ(X, U)) :
    IsOpen {z | ⊤ ≤ F z ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun z => valAt' (F z) U f) {z | ⊤ ≤ F z ⁻¹ᵁ U} := by sorry
