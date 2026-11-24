-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_ker_genPt_faef97509c8e
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_ker_genPt_faef97509c8e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:28.684112+00:00
-- url     : https://prove2.me/theorems/e95d556e-cac7-4d7e-843a-4bc5935f43ab
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR ker gen Pt faef97509c8e: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR ker gen Pt faef97
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR ker gen Pt faef97509c8e construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR ker gen Pt faef97509c8e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/TrivBundleIsTwistedForms.lean#L295-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/TrivBundleIsTwistedForms.lean#L295-L297

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
universe u v w u₁ u₂
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {o}
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_ker_genPt_faef97509c8e (R : Type*) [CommRing R] [IsDomain R] :
    RingHom.ker (genPt R ι) = ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«NumbersDVR».«ker_genPt» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_ker_genPt_faef97509c8e
