-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_algHom
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.norm_algHom
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:10.986685+00:00
-- url     : https://prove2.me/theorems/fc24995d-832c-54e0-be1d-fa287e5c5de1
-- title:
--   Local Class Field: norm alg Hom
-- statement:
--   The Local Class Field construction uses the norm alg Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsA.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsA.lean#L60-L64

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsA
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
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.norm_algHom {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ : E →ₐ[ℚ_[p]] PadicAlgCl p) (x : E) :
    ‖σ x‖ = ‖(x : PadicAlgCl p)‖ := by sorry
