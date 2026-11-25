-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_uval_sub
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.uval_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:03:08.629675+00:00
-- url     : https://prove2.me/theorems/d27930d5-4d93-4825-ac86-2cf8922e47c3
-- title:
--   Local Class Field: uval sub
-- statement:
--   The Local Class Field construction uses the uval sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandF.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandF.lean#L23-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandF
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
variable [(subG p K L).Normal]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.uval_sub (a b : (layerU p K L).V) : uval (a - b) = uval a * (uval b)⁻¹ := by sorry
