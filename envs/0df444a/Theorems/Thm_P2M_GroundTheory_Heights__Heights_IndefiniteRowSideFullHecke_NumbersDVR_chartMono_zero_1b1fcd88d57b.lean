-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_chartMono_zero_1b1fcd88d57b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_chartMono_zero_1b1fcd88d57b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:12.251804+00:00
-- url     : https://prove2.me/theorems/e348258f-4a77-431c-b96e-f7d190329816
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR chart Mono zero 1b1fcd88d57b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR chart Mono z
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR chart Mono zero 1b1fcd88d57b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Numbers DVR chart Mono zero 1b1fcd88d57b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/TrivBundleIsTwistedForms.lean#L252-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/TrivBundleIsTwistedForms.lean#L252-L253

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
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_chartMono_zero_1b1fcd88d57b (pt : MRingOver o ι →ₐ[o] Ω) (i : (k : K) → ι k) : chartMono pt i 0 = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«NumbersDVR».«chartMono_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_chartMono_zero_1b1fcd88d57b
