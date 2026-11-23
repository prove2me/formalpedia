-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_rep_mul__0df8de4ab8c8
-- name    : P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_rep_mul__0df8de4ab8c8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:04.905674+00:00
-- url     : https://prove2.me/theorems/92720120-721a-4ffb-9621-6aeb7ef27fd0
-- title:
--   P2 M Reciprocity Theory Discrete Groups Local Class Field Deg2 rep mul  0df8de4ab8c8: P2 M Reciprocity Theory Discrete Groups Local Class Field Deg2 rep mul  0df8de4ab8c8
-- statement:
--   The P2 M Reciprocity Theory Discrete Groups Local Class Field Deg2 rep mul  0df8de4ab8c8 construction uses the P2 M Reciprocity Theory Discrete Groups Local Class Field Deg2 rep mul  0df8de4ab8c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/CurriedCoboundaryEq.lean#L66-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/CurriedCoboundaryEq.lean#L66-L66

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_IsTwoCocycleCoboundary
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_CurriedCoboundaryEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Coh.CohomologyFunctoriality₂ ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : TRep R G) (N : Subgroup G)

theorem P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_rep_mul__0df8de4ab8c8 (n : G) (hn : n ∈ N) (g : G) : rep N (n * g) = rep N g := by sorry

alias «ReciprocityTheory».«DiscreteGroups».«LocalClassField».«Deg2».«rep_mul'» := P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_rep_mul__0df8de4ab8c8
