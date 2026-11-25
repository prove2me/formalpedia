-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_pow_uniformiser
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.norm_pow_uniformiser
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T16:58:27.782165+00:00
-- url     : https://prove2.me/theorems/578a0f42-97a4-4afc-b27c-6b6e41b2d96c
-- title:
--   Local Class Field: norm pow uniformiser
-- statement:
--   The Local Class Field construction uses the norm pow uniformiser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsF.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsF.lean#L48-L52

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.norm_pow_uniformiser (hK : FiniteDimensional ℚ_[p] K) {π : Kˣ} (hπ : vK p K π = 1) (i : ℕ) :
    ‖((π : K) : PadicAlgCl p)‖ ^ i = (p : ℝ) ^ (- (i : ℝ) / eK p K) := by sorry
