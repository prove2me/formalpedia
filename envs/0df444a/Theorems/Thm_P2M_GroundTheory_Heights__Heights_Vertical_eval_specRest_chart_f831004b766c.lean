-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_eval_specRest_chart_f831004b766c
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_eval_specRest_chart_f831004b766c
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:43:09.493404+00:00
-- url     : https://prove2.me/theorems/8574c9c4-36be-408e-a486-cbe6ed802054
-- title:
--   P2 M Ground Theory Heights  Heights Vertical eval spec Rest chart f831004b766c: P2 M Ground Theory Heights  Heights Vertical eval spec Rest chart f831004b766c
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical eval spec Rest chart f831004b766c construction uses the P2 M Ground Theory Heights  Heights Vertical eval spec Rest chart f831004b766c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormIdentity.lean#L33-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormIdentity.lean#L33-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_eval_specRest_chart_f831004b766c (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) :
    eval (fun j => parYF K e n (.inr j))
        (specRest (kToFrac K e n) (g.map (algebraMap (𝓞 K) K)) (parYF K e n)) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (rename (chartVar e n) g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«eval_specRest_chart» := P2M_GroundTheory_Heights__Heights_Vertical_eval_specRest_chart_f831004b766c
