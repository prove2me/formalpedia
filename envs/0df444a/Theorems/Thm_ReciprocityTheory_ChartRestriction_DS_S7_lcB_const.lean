-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lcB_const
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.lcB_const
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:50:41.68269+00:00
-- url     : https://prove2.me/theorems/1dcc420c-dea8-5817-9c62-958263617e7e
-- title:
--   S7: lc B const
-- statement:
--   The S7 construction uses the lc B const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/LocalB.lean#L82-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/LocalB.lean#L82-L96

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LocalB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology Set
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ReciprocityTheory.ChartRestriction.DS.S7.lcB_const (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hUo : IsOpen U)
    (hdiff : DifferentiableOn ℂ (psM T μ) U) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hid : ∀ z ∈ U, fderiv ℂ (psM T μ) z (z * Y) = -(T.dτ Y * psM T μ z))
    (hY : inK ε Y) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) (hmul : ∀ s t, γ (s + t) = γ s * γ t)
    (A : Matrix (Fin n) (Fin n) ℂ) (hpath : ∀ t ∈ Icc (0 : ℝ) 1, A * NormedSpace.exp ((t : ℂ) • Y) ∈ U) :
    T.op (γ 1) * psM T μ (A * NormedSpace.exp Y) = psM T μ A := by sorry
