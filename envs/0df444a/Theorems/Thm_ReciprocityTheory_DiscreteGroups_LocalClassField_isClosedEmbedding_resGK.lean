-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isClosedEmbedding_resGK
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.isClosedEmbedding_resGK
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:19.385841+00:00
-- url     : https://prove2.me/theorems/8cb49c12-b9a6-4fbb-b88b-5c0b848a2548
-- title:
--   Local Class Field: is Closed Embedding res GK
-- statement:
--   The Local Class Field construction uses the is Closed Embedding res GK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L164-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L164-L165

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.isClosedEmbedding_resGK (h : K ≤ L) : Topology.IsClosedEmbedding (resGK h) := by sorry
