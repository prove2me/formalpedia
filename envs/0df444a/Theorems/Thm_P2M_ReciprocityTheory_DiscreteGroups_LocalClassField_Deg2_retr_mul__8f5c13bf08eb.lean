-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_retr_mul__8f5c13bf08eb
-- name    : P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_retr_mul__8f5c13bf08eb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:14.486141+00:00
-- url     : https://prove2.me/theorems/6e595527-813f-4abd-9cef-6f26663cd9ef
-- title:
--   P2 M Reciprocity Theory Discrete Groups Local Class Field Deg2 retr mul  8f5c13bf08eb: P2 M Reciprocity Theory Discrete Groups Local Class Field Deg2 retr mul  8f5c13bf08eb
-- statement:
--   The P2 M Reciprocity Theory Discrete Groups Local Class Field Deg2 retr mul  8f5c13bf08eb construction uses the P2 M Reciprocity Theory Discrete Groups Local Class Field Deg2 retr mul  8f5c13bf08eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/CurriedCoboundaryEq.lean#L63-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/CurriedCoboundaryEq.lean#L63-L64

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

theorem P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_retr_mul__8f5c13bf08eb (n : G) (hn : n ∈ N) (g : G) : (retr N (n * g) : G) = n * retr N g := by sorry

alias «ReciprocityTheory».«DiscreteGroups».«LocalClassField».«Deg2».«retr_mul'» := P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_retr_mul__8f5c13bf08eb
