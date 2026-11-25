-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_pow_mul_aeval_eq_0699d72cc976
-- name    : P2M_GroundTheory_Heights__Heights_ChartKernel_pow_mul_aeval_eq_0699d72cc976
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:57.558038+00:00
-- url     : https://prove2.me/theorems/6d4bb015-c2e4-41aa-bbdb-ae5ce2548731
-- title:
--   P2 M Ground Theory Heights  Heights Chart Kernel pow mul aeval eq 0699d72cc976: P2 M Ground Theory Heights  Heights Chart Kernel pow mul aeval eq 0699d72cc976
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Kernel pow mul aeval eq 0699d72cc976 construction uses the P2 M Ground Theory Heights  Heights Chart Kernel pow mul aeval eq 0699d72cc976 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L32-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L32-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel
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
open GroundTheory.Heights₂.Heights.ChartKernel
variable {F : Type} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartKernel_pow_mul_aeval_eq_0699d72cc976 {K : Type*} [Field K] [Algebra F K] (t : Fin n → F) (ξ : Fin n → K)
    (hτ : aeval ξ (linForm t) ≠ 0) (g : MvPolynomial (Fin n) F) :
    aeval ξ (linForm t) ^ g.totalDegree * aeval ((aeval ξ (linForm t))⁻¹ • ξ) g =
      aeval ξ (∑ d ∈ Finset.range (g.totalDegree + 1),
        linForm t ^ (g.totalDegree - d) * homogeneousComponent d g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartKernel».«pow_mul_aeval_eq» := P2M_GroundTheory_Heights__Heights_ChartKernel_pow_mul_aeval_eq_0699d72cc976
