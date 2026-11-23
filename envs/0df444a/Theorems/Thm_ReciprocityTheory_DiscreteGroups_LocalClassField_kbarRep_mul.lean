-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_kbarRep_mul
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.kbarRep_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:35.368811+00:00
-- url     : https://prove2.me/theorems/2c3f8ad6-78a3-4e7d-aff5-e1312f7b44f8
-- title:
--   Local Class Field: kbar Rep mul
-- statement:
--   The Local Class Field construction uses the kbar Rep mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean#L17-L19

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.kbarRep_mul (σ τ : GK p K) (y : KbarMult p) :
    kbarRep p K (σ * τ) y = kbarRep p K σ (kbarRep p K τ y) := by sorry
