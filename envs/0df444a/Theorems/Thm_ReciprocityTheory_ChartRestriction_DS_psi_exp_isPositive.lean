-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_psi_exp_isPositive
-- name    : ReciprocityTheory.ChartRestriction.DS.psi_exp_isPositive
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:33:09.848353+00:00
-- url     : https://prove2.me/theorems/39d64a83-ee87-4aaa-ab55-d491937cf23a
-- title:
--   DS: psi exp is Positive
-- statement:
--   The DS construction uses the psi exp is Positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/PsiPos.lean#L103-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/PsiPos.lean#L103-L127

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

theorem ReciprocityTheory.ChartRestriction.DS.psi_exp_isPositive {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (μ : Fin n → ℤ) (hμ : S7.IsMu lam μ)
    (hform : ∀ X, inP ε X → Ψ (NormedSpace.exp X) =
      ((Module.finrank ℂ T.V : ℂ) / ((S7.muK ε Set.univ).toReal : ℂ)) •
        ∫ k, S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k)⁻¹ • (T.op k * S7.projW T * T.op k⁻¹)
          ∂(S7.muK ε)) :
    ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive := by sorry
