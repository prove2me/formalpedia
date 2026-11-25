-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_normalOpenMapping_local_fin_e3b173e5219f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_normalOpenMapping_local_fin_e3b173e5219f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:33:49.803671+00:00
-- url     : https://prove2.me/theorems/84eae40c-fcd5-548c-8317-89823e6da4eb
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets normal Open Mapping local fin e3b173e5219f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex S
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets normal Open Mapping local fin e3b173e5219f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets normal Open Mapping local fin e3b173e5219f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalOpenMapping.lean#L38-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalOpenMapping.lean#L38-L206

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalOpenMapping
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalOpenMapping
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
open MvPolynomial Topology Metric Matrix

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_normalOpenMapping_local_fin_e3b173e5219f
    (hNLI : NormalLocallyIrreducible.Statement)
    (hLNN : GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.Statement)
    (hFB : GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.Statement)
    (hDC : GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.Statement)
    (hIFO : HolomorphicIsolatedFibreOpen.Statement)
    {n k : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (U : Set (Fin k → ℂ)) (φ : (Fin k → ℂ) → Fin n → ℂ)
    (hI : I.IsPrime) (hic : IsIntegrallyClosed (MvPolynomial (Fin n) ℂ ⧸ I))
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = (k : ℕ)) (hU : IsOpen U)
    (hφ : DifferentiableOn ℂ φ U) (hinj : Set.InjOn φ U) (hmaps : Set.MapsTo φ U (zeroSetIn I))
    (u₀ : Fin k → ℂ) (hu₀ : u₀ ∈ U) :
    ∃ B : Set (Fin n → ℂ), IsOpen B ∧ φ u₀ ∈ B ∧ zeroSetIn I ∩ B ⊆ φ '' U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«normalOpenMapping_local_fin» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_normalOpenMapping_local_fin_e3b173e5219f
