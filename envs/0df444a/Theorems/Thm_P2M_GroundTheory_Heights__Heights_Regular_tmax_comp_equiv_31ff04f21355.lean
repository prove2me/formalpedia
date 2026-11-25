-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_tmax_comp_equiv_31ff04f21355
-- name    : P2M_GroundTheory_Heights__Heights_Regular_tmax_comp_equiv_31ff04f21355
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:19:20.265277+00:00
-- url     : https://prove2.me/theorems/5b941bab-6217-472e-833b-c622aa364fc9
-- title:
--   P2 M Ground Theory Heights  Heights Regular tmax comp equiv 31ff04f21355: P2 M Ground Theory Heights  Heights Regular tmax comp equiv 31ff04f21355
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular tmax comp equiv 31ff04f21355 construction uses the P2 M Ground Theory Heights  Heights Regular tmax comp equiv 31ff04f21355 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/RegMaxReindex.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/RegMaxReindex.lean#L29-L33

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

theorem P2M_GroundTheory_Heights__Heights_Regular_tmax_comp_equiv_31ff04f21355 {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [Nonempty ι]
    (e : κ ≃ ι) (t : ι → ℝ) : tmax (t ∘ e) = tmax t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«tmax_comp_equiv» := P2M_GroundTheory_Heights__Heights_Regular_tmax_comp_equiv_31ff04f21355
