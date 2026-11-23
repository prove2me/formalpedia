-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_discreteTopology_GalLK
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.discreteTopology_GalLK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:34.804824+00:00
-- url     : https://prove2.me/theorems/34a4230d-cb89-4738-b1f9-9bc0a8ec079b
-- title:
--   Local Class Field: discrete Topology Gal LK
-- statement:
--   The Local Class Field construction uses the discrete Topology Gal LK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L235-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L235-L236

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
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
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.discreteTopology_GalLK (hL : FiniteDimensional ℚ_[p] L) : DiscreteTopology (GalLK p K L) := by sorry
