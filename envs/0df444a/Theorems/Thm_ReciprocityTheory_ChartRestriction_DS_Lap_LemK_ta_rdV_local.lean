-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_ta_rdV_local
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.LemK.ta_rdV_local
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:46:32.202122+00:00
-- url     : https://prove2.me/theorems/ee5639da-21cf-5ece-b71e-2d02738a8898
-- title:
--   Lem K: ta rd V local
-- statement:
--   The Lem K construction uses the ta rd V local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/KTypeLemma/TransferA.lean#L109-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/KTypeLemma/TransferA.lean#L109-L132

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ReciprocityTheory.ChartRestriction.DS.Lap.LemK.ta_rdV_local (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {W : Set (Matrix (Fin n) (Fin n) ℂ)} {m g X : Matrix (Fin n) (Fin n) ℂ}
    (hW : IsOpen W) (hg : g ∈ W) (hgu : inUJ ε g) (hX : inG ε X)
    (hF : DifferentiableAt ℂ F (g⁻¹ * m)) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : ∀ h ∈ W, inUJ ε h → f h = F (h⁻¹ * m)) :
    RdV X f g = fderiv ℂ F (g⁻¹ * m) (-X * (g⁻¹ * m)) := by sorry
