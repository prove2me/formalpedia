-- Prove2me | Theorems.Thm_P2M_GlobalTheory_EtaleFamily_analyticAt_eval_Hom_fee2a9f1ec8a
-- name    : P2M_GlobalTheory_EtaleFamily_analyticAt_eval_Hom_fee2a9f1ec8a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:30.08102+00:00
-- url     : https://prove2.me/theorems/0ff2afa8-d8b0-476b-841a-10bb30664e8e
-- title:
--   P2 M Global Theory Etale Family analytic At eval Hom fee2a9f1ec8a: P2 M Global Theory Etale Family analytic At eval Hom fee2a9f1ec8a
-- statement:
--   The P2 M Global Theory Etale Family analytic At eval Hom fee2a9f1ec8a construction uses the P2 M Global Theory Etale Family analytic At eval Hom fee2a9f1ec8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHolomorphicSections.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHolomorphicSections.lean#L18-L27

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

theorem P2M_GlobalTheory_EtaleFamily_analyticAt_eval_Hom_fee2a9f1ec8a {E R J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CommRing R]
    (φ : E → (R →+* ℂ)) (u : E → J → ℂ) (w : E) (hφ : ∀ a, AnalyticAt ℂ (fun z => φ z a) w)
    (hu : ∀ i, AnalyticAt ℂ (fun z => u z i) w) (q : MvPolynomial J R) :
    AnalyticAt ℂ (fun z => MvPolynomial.eval₂Hom (φ z) (u z) q) w := by sorry

alias «GlobalTheory».«EtaleFamily».«analyticAt_eval₂Hom» := P2M_GlobalTheory_EtaleFamily_analyticAt_eval_Hom_fee2a9f1ec8a
