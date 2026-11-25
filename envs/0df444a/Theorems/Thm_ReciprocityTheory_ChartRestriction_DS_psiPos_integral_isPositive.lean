-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_psiPos_integral_isPositive
-- name    : ReciprocityTheory.ChartRestriction.DS.psiPos_integral_isPositive
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:53:46.694326+00:00
-- url     : https://prove2.me/theorems/f923459f-d6b2-5f30-807c-9c827295fe21
-- title:
--   DS: psi Pos integral is Positive
-- statement:
--   The DS construction uses the psi Pos integral is Positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/PsiPos.lean#L39-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/PsiPos.lean#L39-L73

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_KinstSecondCountable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_PsiPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
open S7
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

theorem ReciprocityTheory.ChartRestriction.DS.psiPos_integral_isPositive (T : KType ε Λ) {c : ℝ} (hc : 0 ≤ c) (g : KG ε → ℝ)
    (hg0 : ∀ k, 0 ≤ g k) :
    ((c : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε)).IsPositive := by sorry
