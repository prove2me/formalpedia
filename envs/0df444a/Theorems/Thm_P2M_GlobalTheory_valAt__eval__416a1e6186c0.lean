-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__eval__416a1e6186c0
-- name    : P2M_GlobalTheory_valAt__eval__416a1e6186c0
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:56:21.763873+00:00
-- url     : https://prove2.me/theorems/d6f2876d-2889-5a46-a1c9-4b59635b58ef
-- title:
--   P2 M Global Theory val At  eval  416a1e6186c0: P2 M Global Theory val At  eval  416a1e6186c0
-- statement:
--   The P2 M Global Theory val At  eval  416a1e6186c0 construction uses the P2 M Global Theory val At  eval  416a1e6186c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsProjectiveModelPolarisedTorusTheta.lean#L62-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsProjectiveModelPolarisedTorusTheta.lean#L62-L88

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AlgebraMapZeroSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsProjectiveModelPolarisedTorusTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory

theorem P2M_GlobalTheory_valAt__eval__416a1e6186c0 {Y : Over (Sp ℂ)} (x : 𝟙_ (Over (Sp ℂ)) ⟶ Y) {U : Y.left.Opens} (h : ⊤ ≤ x.left ⁻¹ᵁ U) {σ : Type}
    (r : σ → Γ(Y.left, U)) (F : MvPolynomial σ ℂ) :
    valAt' x.left U (MvPolynomial.eval₂ (RingHom.comp (Y.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) = MvPolynomial.eval (fun c => valAt' x.left U (r c)) F := by sorry

alias «GlobalTheory».«valAt'_eval₂» := P2M_GlobalTheory_valAt__eval__416a1e6186c0
