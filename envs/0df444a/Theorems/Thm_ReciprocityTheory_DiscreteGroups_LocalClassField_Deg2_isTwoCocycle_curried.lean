-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_isTwoCocycle_curried
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.isTwoCocycle_curried
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:33.979859+00:00
-- url     : https://prove2.me/theorems/3393862d-0bfe-4cd7-bce2-6492b5857dde
-- title:
--   Deg2: is Two Cocycle curried
-- statement:
--   The Deg2 construction uses the is Two Cocycle curried property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/CurriedCoboundaryEq.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/CurriedCoboundaryEq.lean#L19-L23

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.isTwoCocycle_curried (M : TRep R G) (x : M.coch.X 2) (hx : M.coch.d 2 x = 0) : IsTwoCocycle M.rho (cur M x) := by sorry
