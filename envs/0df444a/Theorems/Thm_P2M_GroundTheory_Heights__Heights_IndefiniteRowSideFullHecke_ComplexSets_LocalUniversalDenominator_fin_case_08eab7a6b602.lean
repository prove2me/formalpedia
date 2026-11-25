-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_LocalUniversalDenominator_fin_case_08eab7a6b602
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_LocalUniversalDenominator_fin_case_08eab7a6b602
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:40:53.596792+00:00
-- url     : https://prove2.me/theorems/ab2dc736-eb5d-4300-8247-d8df086a49ea
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Local Universal Denominator fin case 08eab7a6b602: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Co
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Local Universal Denominator fin case 08eab7a6b602 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Local Universal Denominator fin case 08eab7a6b602 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalUniversalDenominator.lean#L162-L489
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalUniversalDenominator.lean#L162-L489

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalUniversalDenominator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRootSumHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsContainOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVanishNearPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalUniversalDenominator
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
open MvPolynomial Topology Filter
noncomputable section
open LocalUniversalDenominator

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_LocalUniversalDenominator_fin_case_08eab7a6b602
    (hcl : GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionCluster.Statement)
    (hrs : GroundTheory.Heights₂.Heights.ComplexSets.RootSumHolomorphic.Statement)
    (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (h : MvPolynomial (Fin n) ℂ) (w : Fin n → ℂ)
    (U : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℂ)
    (hI : I.IsPrime) (hh : h ∉ I) (hw : w ∈ zeroSetIn I) (hU : U ∈ 𝓝 w)
    (hf : HolomorphicOnSubset f ((zeroSetIn I ∩ U) \ {z | eval z h = 0}))
    (hb : Bornology.IsBounded (f '' ((zeroSetIn I ∩ U) \ {z | eval z h = 0}))) :
    ∃ g : MvPolynomial (Fin n) ℂ, g ∉ I ∧ ∃ N : Set (Fin n → ℂ), IsOpen N ∧ w ∈ N ∧ N ⊆ U ∧
      ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F N ∧
        ∀ z ∈ (zeroSetIn I ∩ N) \ {z | eval z h = 0}, eval z g * f z = F z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«LocalUniversalDenominator».«fin_case» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_LocalUniversalDenominator_fin_case_08eab7a6b602
