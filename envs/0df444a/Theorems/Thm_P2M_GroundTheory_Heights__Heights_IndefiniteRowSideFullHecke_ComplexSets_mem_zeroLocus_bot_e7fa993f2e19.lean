-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_zeroLocus_bot_e7fa993f2e19
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_zeroLocus_bot_e7fa993f2e19
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:07.845799+00:00
-- url     : https://prove2.me/theorems/a26d247d-9d16-45c0-9082-a169ca7242c8
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mem zero Locus bot e7fa993f2e19: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mem zer
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mem zero Locus bot e7fa993f2e19 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mem zero Locus bot e7fa993f2e19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/EqZeroOfMemZeroLocusLineOriginIdeal.lean#L180-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/EqZeroOfMemZeroLocusLineOriginIdeal.lean#L180-L183

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_zeroLocus_bot_e7fa993f2e19 {n : ℕ} (x : Fin n → ℂ) : x ∈ zeroLocus (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«mem_zeroLocus_bot» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_zeroLocus_bot_e7fa993f2e19
