-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TorusEnd_valAt__eval__5db942836e7d
-- name    : P2M_GlobalTheory_TorusEnd_valAt__eval__5db942836e7d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:54.194086+00:00
-- url     : https://prove2.me/theorems/a211fe3a-a000-4c56-abd2-9fae1974a63e
-- title:
--   P2 M Global Theory Torus End val At  eval  5db942836e7d: P2 M Global Theory Torus End val At  eval  5db942836e7d
-- statement:
--   The P2 M Global Theory Torus End val At  eval  5db942836e7d construction uses the P2 M Global Theory Torus End val At  eval  5db942836e7d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsTopLePreimageOfISupEqTop.lean#L31-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsTopLePreimageOfISupEqTop.lean#L31-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTopLePreimageOfISupEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.TorusEnd

theorem P2M_GlobalTheory_TorusEnd_valAt__eval__5db942836e7d {X : Over (Sp ℂ)} {κ : Type*} (x : 𝟙_ (Over (Sp ℂ)) ⟶ X) (U : X.left.Opens)
    (h : ⊤ ≤ x.left ⁻¹ᵁ U) (r : κ → Γ(X.left, U)) (P : MvPolynomial κ ℂ) :
    valAt' x.left U (MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r P) = MvPolynomial.eval (fun i => valAt' x.left U (r i)) P := by sorry

alias «GlobalTheory».«TorusEnd».«valAt'_eval₂» := P2M_GlobalTheory_TorusEnd_valAt__eval__5db942836e7d
