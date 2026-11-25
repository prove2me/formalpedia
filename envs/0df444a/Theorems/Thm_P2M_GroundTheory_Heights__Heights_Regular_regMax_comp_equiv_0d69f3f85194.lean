-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_regMax_comp_equiv_0d69f3f85194
-- name    : P2M_GroundTheory_Heights__Heights_Regular_regMax_comp_equiv_0d69f3f85194
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:34.911873+00:00
-- url     : https://prove2.me/theorems/371bcd87-41b4-4bc6-91e3-e100c83560a9
-- title:
--   P2 M Ground Theory Heights  Heights Regular reg Max comp equiv 0d69f3f85194: P2 M Ground Theory Heights  Heights Regular reg Max comp equiv 0d69f3f85194
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular reg Max comp equiv 0d69f3f85194 construction uses the P2 M Ground Theory Heights  Heights Regular reg Max comp equiv 0d69f3f85194 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/RegMaxReindex.lean#L35-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/RegMaxReindex.lean#L35-L52

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

theorem P2M_GroundTheory_Heights__Heights_Regular_regMax_comp_equiv_0d69f3f85194 {κ ι : Type} [Fintype κ] [Nonempty κ] [Fintype ι] [Nonempty ι]
    (e : κ ≃ ι) (η : ℝ) (t : ι → ℝ) : regMax η (t ∘ e) = regMax η t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«regMax_comp_equiv» := P2M_GroundTheory_Heights__Heights_Regular_regMax_comp_equiv_0d69f3f85194
