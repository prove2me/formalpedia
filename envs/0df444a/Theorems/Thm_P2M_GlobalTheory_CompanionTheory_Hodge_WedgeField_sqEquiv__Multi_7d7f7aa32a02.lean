-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hodge_WedgeField_sqEquiv__Multi_7d7f7aa32a02
-- name    : P2M_GlobalTheory_CompanionTheory_Hodge_WedgeField_sqEquiv__Multi_7d7f7aa32a02
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:24.608595+00:00
-- url     : https://prove2.me/theorems/2b507470-611f-4032-99f8-17b0f49799b7
-- title:
--   P2 M Global Theory Companion Theory Hodge Wedge Field sq Equiv  Multi 7d7f7aa32a02: P2 M Global Theory Companion Theory Hodge Wedge Field sq Equiv  Multi 7d7f7aa32a02
-- statement:
--   The P2 M Global Theory Companion Theory Hodge Wedge Field sq Equiv  Multi 7d7f7aa32a02 construction uses the P2 M Global Theory Companion Theory Hodge Wedge Field sq Equiv  Multi 7d7f7aa32a02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeOfBijective.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeOfBijective.lean#L46-L53

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.WedgeField

theorem P2M_GlobalTheory_CompanionTheory_Hodge_WedgeField_sqEquiv__Multi_7d7f7aa32a02 {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N) (a b : M) :
    sqEquiv E (exteriorPower.ιMulti R 2 ![a, b]) = exteriorPower.ιMulti R 2 ![E a, E b] := by sorry

alias «GlobalTheory».«CompanionTheory».«Hodge».«WedgeField».«sqEquiv_ιMulti» := P2M_GlobalTheory_CompanionTheory_Hodge_WedgeField_sqEquiv__Multi_7d7f7aa32a02
