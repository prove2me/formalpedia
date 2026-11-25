-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AbCoh_TwoFormSum__Multi_two_bb841c234bcc
-- name    : P2M_GlobalTheory_AbCoh_TwoFormSum__Multi_two_bb841c234bcc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:47.301856+00:00
-- url     : https://prove2.me/theorems/691273c6-4614-5dd2-bc38-2eff825045b5
-- title:
--   P2 M Global Theory Ab Coh Two Form Sum  Multi two bb841c234bcc: P2 M Global Theory Ab Coh Two Form Sum  Multi two bb841c234bcc
-- statement:
--   The P2 M Global Theory Ab Coh Two Form Sum  Multi two bb841c234bcc construction uses the P2 M Global Theory Ab Coh Two Form Sum  Multi two bb841c234bcc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlobalTwoFormEqSumWedgeGlobalOneForms.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlobalTwoFormEqSumWedgeGlobalOneForms.lean#L29-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlobalTwoFormEqSumWedgeGlobalOneForms
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.TwoFormSum
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem P2M_GlobalTheory_AbCoh_TwoFormSum__Multi_two_bb841c234bcc (v : Fin 2 → Ω[B⁄R]) : exteriorPower.ιMulti B 2 v = wedge R B (v 0) (v 1) := by sorry

alias «GlobalTheory».«AbCoh».«TwoFormSum».«ιMulti_two» := P2M_GlobalTheory_AbCoh_TwoFormSum__Multi_two_bb841c234bcc
