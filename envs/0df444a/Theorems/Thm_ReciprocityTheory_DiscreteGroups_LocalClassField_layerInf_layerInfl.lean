-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_layerInf_layerInfl
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.layerInf_layerInfl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:49.783808+00:00
-- url     : https://prove2.me/theorems/38726bdf-b81f-4da9-8aad-b5a0b0d98f39
-- title:
--   Local Class Field: layer Inf layer Infl
-- statement:
--   The Local Class Field construction uses the layer Inf layer Infl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/EqZeroOfMemBrKerOfCoprime.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/EqZeroOfMemBrKerOfCoprime.lean#L19-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RestrictedMultiplicativeH1Subsingleton
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_EqZeroOfResEqZeroOfCoprime
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_EqZeroOfMemBrKerOfCoprime
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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.layerInf_layerInfl {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') [(subG p K L).Normal]
    [(subG p K L').Normal] (n : ℕ) (x : (layer p K L).H n) :
    (layerInf p K L').hom.H n ((layerInfl h).hom.H n x) = (layerInf p K L).hom.H n x := by sorry
