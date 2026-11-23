-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ArtinKernel_evalPt__eq_aeda6690487c
-- name    : P2M_GlobalTheory_ArtinKernel_evalPt__eq_aeda6690487c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:11:34.335588+00:00
-- url     : https://prove2.me/theorems/98c71ee0-8910-411f-ae0c-1be8d6511d88
-- title:
--   P2 M Global Theory Artin Kernel eval Pt  eq aeda6690487c: P2 M Global Theory Artin Kernel eval Pt  eq aeda6690487c
-- statement:
--   The P2 M Global Theory Artin Kernel eval Pt  eq aeda6690487c construction uses the P2 M Global Theory Artin Kernel eval Pt  eq aeda6690487c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/DifferentiableOnFamPtAffine.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/DifferentiableOnFamPtAffine.lean#L43-L46

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfMulPeriod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnFamPtAffine
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
noncomputable section
open GlobalTheory GlobalTheory.ArtinKernel
open GlobalTheory.TangentOrigin
variable {R : Type} [CommRing R] {X Y : Scheme.{0}}

theorem P2M_GlobalTheory_ArtinKernel_evalPt__eq_aeda6690487c (x : Sp R ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    evalPt' x U f = evalPt x U h f := by sorry

alias «GlobalTheory».«ArtinKernel».«evalPt'_eq» := P2M_GlobalTheory_ArtinKernel_evalPt__eq_aeda6690487c
