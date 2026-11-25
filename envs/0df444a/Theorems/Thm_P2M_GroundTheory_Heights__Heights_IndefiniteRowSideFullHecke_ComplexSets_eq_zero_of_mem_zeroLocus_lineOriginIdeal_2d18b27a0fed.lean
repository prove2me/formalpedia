-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_zero_of_mem_zeroLocus_lineOriginIdeal_2d18b27a0fed
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_zero_of_mem_zeroLocus_lineOriginIdeal_2d18b27a0fed
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:20:57.468384+00:00
-- url     : https://prove2.me/theorems/bd104dd9-68dc-4dad-907d-e91f9dad3bb7
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eq zero of mem zero Locus line Origin Ideal 2d18b27a0fed: P2 M Ground Theory Heights  Heights Indefinite Row Side Full H
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eq zero of mem zero Locus line Origin Ideal 2d18b27a0fed construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eq zero of mem zero Locus line Origin Ideal 2d18b27a0fed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/EqZeroOfMemZeroLocusLineOriginIdeal.lean#L296-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/EqZeroOfMemZeroLocusLineOriginIdeal.lean#L296-L301

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
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
open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff ENNReal
noncomputable section
variable {n d e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_zero_of_mem_zeroLocus_lineOriginIdeal_2d18b27a0fed {q : Fin 1 → ℂ} (hq : q ∈ zeroLocus lineOriginIdeal) : q = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«eq_zero_of_mem_zeroLocus_lineOriginIdeal» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_zero_of_mem_zeroLocus_lineOriginIdeal_2d18b27a0fed
