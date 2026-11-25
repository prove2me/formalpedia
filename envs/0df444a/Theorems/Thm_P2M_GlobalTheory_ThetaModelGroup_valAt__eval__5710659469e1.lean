-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ThetaModelGroup_valAt__eval__5710659469e1
-- name    : P2M_GlobalTheory_ThetaModelGroup_valAt__eval__5710659469e1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:11:07.188271+00:00
-- url     : https://prove2.me/theorems/d88194d4-5ec4-4920-889a-a70c76683da0
-- title:
--   P2 M Global Theory Theta Model Group val At  eval  5710659469e1: P2 M Global Theory Theta Model Group val At  eval  5710659469e1
-- statement:
--   The P2 M Global Theory Theta Model Group val At  eval  5710659469e1 construction uses the P2 M Global Theory Theta Model Group val At  eval  5710659469e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/LocallyOfFiniteTypeTensor.lean#L146-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/LocallyOfFiniteTypeTensor.lean#L146-L155

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LocallyOfFiniteTypeTensor
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
open GlobalTheory.ThetaModelGroup
variable {X Y : Over (Sp ℂ)}

theorem P2M_GlobalTheory_ThetaModelGroup_valAt__eval__5710659469e1 {κ : Type} (x : 𝟙_ (Over (Sp ℂ)) ⟶ X) (U : X.left.Opens) (h : ⊤ ≤ x.left ⁻¹ᵁ U)
    (r : κ → Γ(X.left, U)) (F : MvPolynomial κ ℂ) :
    valAt' x.left U (MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) = MvPolynomial.eval (fun c => valAt' x.left U (r c)) F := by sorry

alias «GlobalTheory».«ThetaModelGroup».«valAt'_eval₂» := P2M_GlobalTheory_ThetaModelGroup_valAt__eval__5710659469e1
