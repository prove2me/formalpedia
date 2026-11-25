-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CapPs_fold_conj
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CapPs.fold_conj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:04:27.920491+00:00
-- url     : https://prove2.me/theorems/41e7dfcf-f36a-5d20-88c3-755053bd20cd
-- title:
--   Cap Ps: fold conj
-- statement:
--   The Cap Ps construction uses the fold conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ChainHSlice.lean#L123-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ChainHSlice.lean#L123-L130

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.CapPs.fold_conj (c : 𝕄 → 𝕄) : ∀ {p : ℕ} (T T' : Fin p → (𝕄 → ℂ) → (𝕄 → ℂ)),
    (∀ i F, T i (fun y => F (c y)) = fun y => T' i F (c y)) → ∀ F : 𝕄 → ℂ,
    (List.ofFn T).foldr (fun t h => t h) (fun y => F (c y)) =
      fun y => (List.ofFn T').foldr (fun t h => t h) F (c y)
  := by sorry
