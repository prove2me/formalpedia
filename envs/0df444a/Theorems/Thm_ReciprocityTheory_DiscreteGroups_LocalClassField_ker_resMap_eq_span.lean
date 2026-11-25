-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_ker_resMap_eq_span
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.ker_resMap_eq_span
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T16:41:16.796018+00:00
-- url     : https://prove2.me/theorems/7c955b6d-ed7a-416a-8bb6-b7a3ce1b158f
-- title:
--   Local Class Field: ker res Map eq span
-- statement:
--   The Local Class Field construction uses the ker res Map eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L119-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L119-L128

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Neutral.Cmp
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
attribute [local instance] zpAlgOK

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.ker_resMap_eq_span (hK : FiniteDimensional ℚ_[p] K) {π : Kˣ} (hπ : vK p K π = 1)
    (hπ1 : (π : K) ∈ OK p K) : RingHom.ker (resMap p K) = Ideal.span {(⟨π, hπ1⟩ : OK p K)} := by sorry
