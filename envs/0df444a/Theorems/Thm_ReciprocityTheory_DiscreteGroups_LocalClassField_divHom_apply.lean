-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_divHom_apply
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.divHom_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:34.393867+00:00
-- url     : https://prove2.me/theorems/c718abd9-29ef-42ca-a0cd-07c69e090069
-- title:
--   Local Class Field: div Hom apply
-- statement:
--   The Local Class Field construction uses the div Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsB.lean#L11-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsB.lean#L11-L11

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.divHom_apply (e : ℕ) (n : ℤ) : divHom e n = n * (e : ℝ)⁻¹ := by sorry
