-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AbCoh_preToPairRes_pre__191ebb21c4d1
-- name    : P2M_GlobalTheory_AbCoh_preToPairRes_pre__191ebb21c4d1
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:11:49.923021+00:00
-- url     : https://prove2.me/theorems/24adbe06-8704-5fb7-ae68-6060adc4ed11
-- title:
--   P2 M Global Theory Ab Coh pre To Pair Res pre  191ebb21c4d1: P2 M Global Theory Ab Coh pre To Pair Res pre  191ebb21c4d1
-- statement:
--   The P2 M Global Theory Ab Coh pre To Pair Res pre  191ebb21c4d1 construction uses the P2 M Global Theory Ab Coh pre To Pair Res pre  191ebb21c4d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CocyclePullbackIffPreimageAffineHom.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CocyclePullbackIffPreimageAffineHom.lean#L81-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocyclePullbackIffPreimageAffineHom
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
open GlobalTheory GlobalTheory.AbCoh
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} {φ : X' ⟶ X} [IsAffineHom φ]
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'}
variable (h : φ ≫ s = s' ≫ spMap σ)

theorem P2M_GlobalTheory_AbCoh_preToPairRes_pre__191ebb21c4d1 (q : (Pair φ)ᵒᵖ) (b : (OAff s).obj ((pairSnd φ).obj q)) :
    (preToPairRes φ s').α q (preα φ s s' ((pairSnd φ).obj q) b) = (pairPull h).α q b := by sorry

alias «GlobalTheory».«AbCoh».«preToPairRes_preα» := P2M_GlobalTheory_AbCoh_preToPairRes_pre__191ebb21c4d1
