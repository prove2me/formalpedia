-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocDomain_linForm_not_mem_sup_ef32ee3b11da
-- name    : P2M_GroundTheory_Heights__Heights_ChartLocDomain_linForm_not_mem_sup_ef32ee3b11da
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:15:47.792906+00:00
-- url     : https://prove2.me/theorems/9b4217c3-324b-4ac2-8a32-26a986690e28
-- title:
--   P2 M Ground Theory Heights  Heights Chart Loc Domain lin Form not mem sup ef32ee3b11da: P2 M Ground Theory Heights  Heights Chart Loc Domain lin Form not mem sup ef32ee3b11da
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Loc Domain lin Form not mem sup ef32ee3b11da construction uses the P2 M Ground Theory Heights  Heights Chart Loc Domain lin Form not mem sup ef32ee3b11da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartLocDomain.lean#L32-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartLocDomain.lean#L32-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocDomain
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
open GroundTheory.Heights₂.Heights.ChartLocDomain
variable {F : Type} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartLocDomain_linForm_not_mem_sup_ef32ee3b11da {I : Ideal (MvPolynomial (Fin n) F)} (hI : IsProjPrime I) {t u : Fin n → F}
    (ht : linForm t ∉ I) (hu : linForm u ∉ I) : linForm u ∉ I ⊔ Ideal.span {linForm t - 1} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLocDomain».«linForm_not_mem_sup» := P2M_GroundTheory_Heights__Heights_ChartLocDomain_linForm_not_mem_sup_ef32ee3b11da
