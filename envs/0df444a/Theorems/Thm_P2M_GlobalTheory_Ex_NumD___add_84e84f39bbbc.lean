-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Ex_NumD___add_84e84f39bbbc
-- name    : P2M_GlobalTheory_Ex_NumD___add_84e84f39bbbc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:56.400837+00:00
-- url     : https://prove2.me/theorems/6aabae1b-7d37-4869-b0be-82386dde030f
-- title:
--   P2 M Global Theory Ex Num D   add 84e84f39bbbc: P2 M Global Theory Ex Num D   add 84e84f39bbbc
-- statement:
--   The P2 M Global Theory Ex Num D   add 84e84f39bbbc construction uses the P2 M Global Theory Ex Num D   add 84e84f39bbbc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L125-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean#L125-L126

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
attribute [instance] NumB.grp
attribute [instance] NumD.add NumD.free NumD.fin
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.NumD
variable (N : NumD O)

theorem P2M_GlobalTheory_Ex_NumD___add_84e84f39bbbc (a b : N.X) : N.ψ (a + b) = N.τ a b * N.ψ a * N.ψ b := by sorry

alias «GlobalTheory».«Ex».«NumD».«ψ_add» := P2M_GlobalTheory_Ex_NumD___add_84e84f39bbbc
