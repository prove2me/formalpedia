-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_normHom_of_infinite
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.normHom_of_infinite
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:56.85001+00:00
-- url     : https://prove2.me/theorems/86c2b004-9ec7-5df3-9672-c6395af86e22
-- title:
--   Local Class Field: norm Hom of infinite
-- statement:
--   The Local Class Field construction uses the norm Hom of infinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean#L28-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean#L28-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.normHom_of_infinite [Infinite (GK p K ⧸ subG p K L)] : normHom p K L = 0 := by sorry
