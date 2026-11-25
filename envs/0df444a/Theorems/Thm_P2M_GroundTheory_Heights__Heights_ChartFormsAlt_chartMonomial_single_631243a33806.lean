-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFormsAlt_chartMonomial_single_631243a33806
-- name    : P2M_GroundTheory_Heights__Heights_ChartFormsAlt_chartMonomial_single_631243a33806
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:18:40.908208+00:00
-- url     : https://prove2.me/theorems/46b62294-4e4a-406c-b24f-0e8f712e1e3a
-- title:
--   P2 M Ground Theory Heights  Heights Chart Forms Alt chart Monomial single 631243a33806: P2 M Ground Theory Heights  Heights Chart Forms Alt chart Monomial single 631243a33806
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Forms Alt chart Monomial single 631243a33806 construction uses the P2 M Ground Theory Heights  Heights Chart Forms Alt chart Monomial single 631243a33806 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExistsFormOfMemChartRing.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExistsFormOfMemChartRing.lean#L27-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExistsFormOfMemChartRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartFormsAlt
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartFormsAlt_chartMonomial_single_631243a33806 (c : (k : ι) → Fin (n k + 1)) (k : ι) :
    chartMonomial c (Pi.single k 1) = X ⟨k, c k⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartFormsAlt».«chartMonomial_single» := P2M_GroundTheory_Heights__Heights_ChartFormsAlt_chartMonomial_single_631243a33806
