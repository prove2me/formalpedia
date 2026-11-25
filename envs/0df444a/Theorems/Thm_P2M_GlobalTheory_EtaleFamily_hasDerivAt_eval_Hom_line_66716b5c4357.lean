-- Prove2me | Theorems.Thm_P2M_GlobalTheory_EtaleFamily_hasDerivAt_eval_Hom_line_66716b5c4357
-- name    : P2M_GlobalTheory_EtaleFamily_hasDerivAt_eval_Hom_line_66716b5c4357
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:06:59.311568+00:00
-- url     : https://prove2.me/theorems/013fba81-80ad-4416-956f-a7794de284d0
-- title:
--   P2 M Global Theory Etale Family has Deriv At eval Hom line 66716b5c4357: P2 M Global Theory Etale Family has Deriv At eval Hom line 66716b5c4357
-- statement:
--   The P2 M Global Theory Etale Family has Deriv At eval Hom line 66716b5c4357 construction uses the P2 M Global Theory Etale Family has Deriv At eval Hom line 66716b5c4357 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHolomorphicSections.lean#L29-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHolomorphicSections.lean#L29-L55

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolomorphicSections
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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.EtaleFamily

theorem P2M_GlobalTheory_EtaleFamily_hasDerivAt_eval_Hom_line_66716b5c4357 {R J : Type*} [CommRing R] [Fintype J]
    (φ : R →+* ℂ) (q : MvPolynomial J R) (y v : J → ℂ) :
    HasDerivAt (fun t : ℂ => MvPolynomial.eval₂Hom φ (y + t • v) q)
      (∑ i, MvPolynomial.eval₂Hom φ y (MvPolynomial.pderiv i q) * v i) 0 := by sorry

alias «GlobalTheory».«EtaleFamily».«hasDerivAt_eval₂Hom_line» := P2M_GlobalTheory_EtaleFamily_hasDerivAt_eval_Hom_line_66716b5c4357
