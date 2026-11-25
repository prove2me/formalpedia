-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_abs_lt_of_k__ne_zero_f718908ff862
-- name    : P2M_GroundTheory_Heights__Heights_Regular_abs_lt_of_k__ne_zero_f718908ff862
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:11.028227+00:00
-- url     : https://prove2.me/theorems/bba44a76-c07f-41d3-86df-c4c56fc4a7b4
-- title:
--   P2 M Ground Theory Heights  Heights Regular abs lt of k  ne zero f718908ff862: P2 M Ground Theory Heights  Heights Regular abs lt of k  ne zero f718908ff862
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular abs lt of k  ne zero f718908ff862 construction uses the P2 M Ground Theory Heights  Heights Regular abs lt of k  ne zero f718908ff862 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/RegMaxReindex.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/RegMaxReindex.lean#L12-L16

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_RegMaxReindex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory
open ReciprocityTheory.AnForm.A (regMax tmax kθ)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_abs_lt_of_k__ne_zero_f718908ff862 {x : ℝ} (h : kθ x ≠ 0) : |x| < 1 / 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«abs_lt_of_kθ_ne_zero» := P2M_GroundTheory_Heights__Heights_Regular_abs_lt_of_k__ne_zero_f718908ff862
