-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_HodgeAlt_alt__Multi_4e0913c07ff2
-- name    : P2M_GlobalTheory_CompanionTheory_HodgeAlt_alt__Multi_4e0913c07ff2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:25:52.561242+00:00
-- url     : https://prove2.me/theorems/b2b421ed-3bef-47b6-9b5c-8d93802fbb61
-- title:
--   P2 M Global Theory Companion Theory Hodge Alt alt  Multi 4e0913c07ff2: P2 M Global Theory Companion Theory Hodge Alt alt  Multi 4e0913c07ff2
-- statement:
--   The P2 M Global Theory Companion Theory Hodge Alt alt  Multi 4e0913c07ff2 construction uses the P2 M Global Theory Companion Theory Hodge Alt alt  Multi 4e0913c07ff2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L131-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L131-L133

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
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
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R V V' W W' : Type} [CommRing R] [AddCommGroup V] [AddCommGroup V'] [AddCommGroup W]
  [AddCommGroup W'] [Module R V] [Module R V'] [Module R W] [Module R W']

theorem P2M_GlobalTheory_CompanionTheory_HodgeAlt_alt__Multi_4e0913c07ff2 (l l' : V →ₗ[R] R) (a b : V) :
    alt l l' (exteriorPower.ιMulti R 2 ![a, b]) = l a * l' b - l' a * l b := by sorry

alias «GlobalTheory».«CompanionTheory».«HodgeAlt».«alt_ιMulti» := P2M_GlobalTheory_CompanionTheory_HodgeAlt_alt__Multi_4e0913c07ff2
