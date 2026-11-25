-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_im_analytic_5240bb34bec0
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_im_analytic_5240bb34bec0
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:40.361337+00:00
-- url     : https://prove2.me/theorems/68a73fbc-b88c-4714-910f-8d09e3b8f4d0
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit levi im analytic 5240bb34bec0: P2 M Ground Theory Heights  Heights Analytic Limit levi im analytic 5240bb34bec0
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit levi im analytic 5240bb34bec0 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit levi im analytic 5240bb34bec0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PGreenMassReplaceLevi.lean#L65-L70

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_PGreenMassReplaceLevi
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul levi_re_analytic)
noncomputable section
variable {ι : Type} [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_im_analytic_5240bb34bec0 {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (w : ι → ℂ) :
    levi (fun z => (S z).im) y w = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«levi_im_analytic» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_im_analytic_5240bb34bec0
