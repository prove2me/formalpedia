-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AbCoh_SpanCup_exists_sum__Multi_5c26d2b22898
-- name    : P2M_GlobalTheory_AbCoh_SpanCup_exists_sum__Multi_5c26d2b22898
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:13:44.133526+00:00
-- url     : https://prove2.me/theorems/7acb9bce-54e1-568a-af17-0b1a314e9dbc
-- title:
--   P2 M Global Theory Ab Coh Span Cup exists sum  Multi 5c26d2b22898: P2 M Global Theory Ab Coh Span Cup exists sum  Multi 5c26d2b22898
-- statement:
--   The P2 M Global Theory Ab Coh Span Cup exists sum  Multi 5c26d2b22898 construction uses the P2 M Global Theory Ab Coh Span Cup exists sum  Multi 5c26d2b22898 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HyperH2GeneratedByCups.lean#L22-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HyperH2GeneratedByCups.lean#L22-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HyperH2SumOfCupsExactStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HyperH2GeneratedByCups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.SpanCup

theorem P2M_GlobalTheory_AbCoh_SpanCup_exists_sum__Multi_5c26d2b22898 {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (w : ⋀[R]^2 M) :
    ∃ (n : ℕ) (x y : Fin n → M), w = ∑ k, exteriorPower.ιMulti R 2 ![x k, y k] := by sorry

alias «GlobalTheory».«AbCoh».«SpanCup».«exists_sum_ιMulti» := P2M_GlobalTheory_AbCoh_SpanCup_exists_sum__Multi_5c26d2b22898
