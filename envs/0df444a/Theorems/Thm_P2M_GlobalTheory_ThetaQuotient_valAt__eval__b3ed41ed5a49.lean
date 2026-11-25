-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ThetaQuotient_valAt__eval__b3ed41ed5a49
-- name    : P2M_GlobalTheory_ThetaQuotient_valAt__eval__b3ed41ed5a49
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:11:22.417334+00:00
-- url     : https://prove2.me/theorems/a120995f-4ed0-4de5-8d22-03a978c3bfe3
-- title:
--   P2 M Global Theory Theta Quotient val At  eval  b3ed41ed5a49: P2 M Global Theory Theta Quotient val At  eval  b3ed41ed5a49
-- statement:
--   The P2 M Global Theory Theta Quotient val At  eval  b3ed41ed5a49 construction uses the P2 M Global Theory Theta Quotient val At  eval  b3ed41ed5a49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/EvalDivOfIsHomogeneous.lean#L29-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/EvalDivOfIsHomogeneous.lean#L29-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EvalDivOfIsHomogeneous
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
open GlobalTheory.ThetaQuotient

theorem P2M_GlobalTheory_ThetaQuotient_valAt__eval__b3ed41ed5a49 {σ : Type*} {X : Over (Sp ℂ)} (x : 𝟙_ (Over (Sp ℂ)) ⟶ X) {U : X.left.Opens}
    (h : ⊤ ≤ x.left ⁻¹ᵁ U) (r : σ → Γ(X.left, U)) (F : MvPolynomial σ ℂ) :
    valAt' x.left U (MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) = MvPolynomial.eval (fun i => valAt' x.left U (r i)) F := by sorry

alias «GlobalTheory».«ThetaQuotient».«valAt'_eval₂» := P2M_GlobalTheory_ThetaQuotient_valAt__eval__b3ed41ed5a49
