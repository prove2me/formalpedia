-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_descend2
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.descend2
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:52:52.813325+00:00
-- url     : https://prove2.me/theorems/be707834-c2aa-4666-9a27-50e96115d57e
-- title:
--   Deg2: descend2
-- statement:
--   The Deg2 construction uses the descend2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HomFInjective.lean#L40-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HomFInjective.lean#L40-L58

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.descend2 (hN : IsOpen (N : Set G)) (hP : IsInvRep M N Q P) (x : M.coch.X 2) (hx : M.coch.d 2 x = 0)
    (h0 : ∀ n ∈ N, ∀ g, cur M x n g = 0 ∧ cur M x g n = 0) :
    ∃ z : Q.coch.X 2, Q.coch.d 2 z = 0 ∧ P.hom.f 2 z = x := by sorry
