-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_exact2
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.exact2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:59:00.229706+00:00
-- url     : https://prove2.me/theorems/9f9aa306-fd08-49b3-9d19-e70a4ced26be
-- title:
--   Deg2: exact2
-- statement:
--   The Deg2 construction uses the exact2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HomFInjective.lean#L60-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HomFInjective.lean#L60-L90

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_CurriedCoboundaryEq
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HomFInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.exact2 (hN : IsOpen (N : Set G)) (hP : IsInvRep M N Q P) (h1 : Subsingleton ((M.resSub N).H 1)) :
    Exact (P.hom.H 2) ((Pair.res M N.subtype continuous_subtype_val).hom.H 2) := by sorry
