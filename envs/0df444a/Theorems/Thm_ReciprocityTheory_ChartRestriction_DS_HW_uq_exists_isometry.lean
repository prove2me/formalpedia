-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_exists_isometry
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.uq_exists_isometry
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:33:34.212374+00:00
-- url     : https://prove2.me/theorems/6934c106-c26f-43ad-9c70-7fe1dadba0f5
-- title:
--   HW: uq exists isometry
-- statement:
--   The HW construction uses the uq exists isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/UniqueA.lean#L301-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/UniqueA.lean#L301-L344

import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open Formalism.REAL
variable {n : ℕ}
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem ReciprocityTheory.ChartRestriction.DS.HW.uq_exists_isometry (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V)
    (F' : Fin n → Fin n → Module.End ℂ V') (Λ : Fin n → ℝ) (w : V) (w' : V')
    (hR : KRel ε F) (hR' : KRel ε F') (hU : KUnit ε F) (hU' : KUnit ε F')
    (hw : KHighest ε F Λ w) (hw' : KHighest ε F' Λ w') (hw1 : ‖w‖ = 1) (hw1' : ‖w'‖ = 1)
    (hT : kSpan ε F w = ⊤) (hT' : kSpan ε F' w' = ⊤) :
    ∃ φ : V ≃ₗᵢ[ℂ] V', (∀ a b, ε a = ε b → ∀ v, φ (F a b v) = F' a b (φ v)) ∧ φ w = w' := by sorry
