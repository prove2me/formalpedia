-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CapPs_qdet_eq_gen
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CapPs.qdet_eq_gen
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:09:43.791444+00:00
-- url     : https://prove2.me/theorems/669d3e3c-76e0-5a87-bd06-588e2643a3cd
-- title:
--   Cap Ps: qdet eq gen
-- statement:
--   The Cap Ps construction uses the qdet eq gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ChainHSlice.lean#L146-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ChainHSlice.lean#L146-L166

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ProdOfFnSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ChainHSlice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CapPs
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
local notation "𝕄" => Matrix (Fin n) (Fin n) ℂ
local notation "𝕋" => Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ} [CompactSpace (KG ε)]

theorem ReciprocityTheory.ChartRestriction.DS.S7.CapPs.qdet_eq_gen (Eop : Fin n → Fin n → (𝕄 → ℂ) → (𝕄 → ℂ)) (A : Fin n → Fin n → Module.End ℂ (smoothS n))
    (hA : ∀ a b (F : 𝕄 → ℂ) (G : smoothS n), Set.EqOn F G (OmegaSet n) →
      Set.EqOn (Eop a b F) ((A a b G : smoothS n) : 𝕄 → ℂ) (OmegaSet n))
    (u : ℂ) (F : 𝕄 → ℂ) (G : smoothS n) (h : Set.EqOn F G (OmegaSet n)) {z : 𝕄} (hz : z ∈ OmegaSet n) :
    Formalism.QuantumDeterminants.qdetOp Eop u F z = ((capelliC A u G : smoothS n) : 𝕄 → ℂ) z := by sorry
