-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_openMapping_of_isIntegrallyClosed_228392ee9e93
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_openMapping_of_isIntegrallyClosed_228392ee9e93
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:40:30.878159+00:00
-- url     : https://prove2.me/theorems/019dfc0e-c0bb-4891-afb0-fe9c06f231c6
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets open Mapping of is Integrally Closed 228392ee9e93: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Co
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets open Mapping of is Integrally Closed 228392ee9e93 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets open Mapping of is Integrally Closed 228392ee9e93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalModelOpenMapping.lean#L132-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalModelOpenMapping.lean#L132-L212

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelOpenMapping
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericProjectionFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsContainOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDiscriminantCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelOpenMapping
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_openMapping_of_isIntegrallyClosed_228392ee9e93 (hirr : NormalLocallyIrreducible.Statement)
    (hoff : BranchOffHypersurface.Statement) (hinj : InjectiveHolomorphicOpen.Statement) {N k : ℕ}
    (I : Ideal (MvPolynomial (Fin N) ℂ)) (hI : I.IsPrime) (hic : IsIntegrallyClosed (MvPolynomial (Fin N) ℂ ⧸ I))
    (hdim : ringKrullDim (MvPolynomial (Fin N) ℂ ⧸ I) = (k : ℕ)) (U : Set (Fin k → ℂ))
    (φ : (Fin k → ℂ) → Fin N → ℂ) (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hφi : Set.InjOn φ U)
    (hφZ : Set.MapsTo φ U (zeroSetIn I)) :
    ∃ O : Set (Fin N → ℂ), IsOpen O ∧ φ '' U = zeroSetIn I ∩ O := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«openMapping_of_isIntegrallyClosed» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_openMapping_of_isIntegrallyClosed_228392ee9e93
