-- Prove2me | Theorems.Thm_P2M_GlobalTheory_KS_Sym_res__3f1ad26b3930
-- name    : P2M_GlobalTheory_KS_Sym_res__3f1ad26b3930
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:07:00.492087+00:00
-- url     : https://prove2.me/theorems/6b855f1e-c404-4393-855c-3821d6196db6
-- title:
--   P2 M Global Theory KS Sym res  3f1ad26b3930: P2 M Global Theory KS Sym res  3f1ad26b3930
-- statement:
--   The P2 M Global Theory KS Sym res  3f1ad26b3930 construction uses the P2 M Global Theory KS Sym res  3f1ad26b3930 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnCompSpMap.lean#L255-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnCompSpMap.lean#L255-L259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstFnCompSpMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Sym
variable {X X₂ Y Z : Scheme.{0}}
variable {K R : Type} [Field K] [CommRing R]

theorem P2M_GlobalTheory_KS_Sym_res__3f1ad26b3930 {q : Y ⟶ Sp K} {s : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {W : X.Opens}
    {d : ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O)} (hd : LocDerK q s m D W d) {O O₁ : X.Opens} (h : O₁ ≤ O)
    (hO : O ≤ W) (f : Γ(X, O)) : d O₁ (rsT f O₁) = rsT (d O f) (m ⁻¹ᵁ O₁) := by sorry

alias «GlobalTheory».«KS».«Sym».«res'» := P2M_GlobalTheory_KS_Sym_res__3f1ad26b3930
