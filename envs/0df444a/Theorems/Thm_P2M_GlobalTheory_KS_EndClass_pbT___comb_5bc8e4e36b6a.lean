-- Prove2me | Theorems.Thm_P2M_GlobalTheory_KS_EndClass_pbT___comb_5bc8e4e36b6a
-- name    : P2M_GlobalTheory_KS_EndClass_pbT___comb_5bc8e4e36b6a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:17:05.910072+00:00
-- url     : https://prove2.me/theorems/f3c9af98-1e96-5e2b-a62a-2ff57b3ea794
-- title:
--   P2 M Global Theory KS End Class pb T   comb 5bc8e4e36b6a: P2 M Global Theory KS End Class pb T   comb 5bc8e4e36b6a
-- statement:
--   The P2 M Global Theory KS End Class pb T   comb 5bc8e4e36b6a construction uses the P2 M Global Theory KS End Class pb T   comb 5bc8e4e36b6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KodairaSpencerClassCohomologousAlongEndomorphism.lean#L104-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KodairaSpencerClassCohomologousAlongEndomorphism.lean#L104-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsAlongGroupHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsBasisVerticalDerivationsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerClassCohomologousAlongEndomorphism
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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.EndClass
variable {X Y Z T : Scheme.{0}}
variable {K : Type} [Field K] {R : Type} [CommRing R] {g : ℕ}

theorem P2M_GlobalTheory_KS_EndClass_pbT___comb_5bc8e4e36b6a {m : Y ⟶ X} (dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)) (y : Z ⟶ Y) (O : Z.Opens)
    {W₀ W : X.Opens} (hO : O ≤ y ⁻¹ᵁ m ⁻¹ᵁ W₀) (hW : W ≤ W₀) (c : Fin g → Γ(Z, O)) (f : Γ(X, W)) :
    pbT O.ι (∑ a, rsT (c a) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W))
      (((O.ι ≫ y) ≫ m) ⁻¹ᵁ W) =
    ∑ a, rsT (pbT O.ι (c a) (((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀)) _ * pbT (O.ι ≫ y) (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by sorry

alias «GlobalTheory».«KS».«EndClass».«pbT_ι_comb» := P2M_GlobalTheory_KS_EndClass_pbT___comb_5bc8e4e36b6a
