-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_kbarRep_out
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.kbarRep_out
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:51.255787+00:00
-- url     : https://prove2.me/theorems/1fed24d9-ed5e-4dd0-8b0e-c7d23b2578f3
-- title:
--   Local Class Field: kbar Rep out
-- statement:
--   The Local Class Field construction uses the kbar Rep out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean#L45-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean#L45-L54

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.kbarRep_out (y : KbarMult p) (hy : y ∈ multOf p L) (σ : GK p K) :
    kbarRep p K (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out y = kbarRep p K σ y := by sorry
