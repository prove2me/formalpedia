-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_eval_specRest_lin_0a2b9807cdd4
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_eval_specRest_lin_0a2b9807cdd4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:43:33.868468+00:00
-- url     : https://prove2.me/theorems/29e164d9-8ec6-4f44-81cd-365f1f0ec022
-- title:
--   P2 M Ground Theory Heights  Heights Vertical eval spec Rest lin 0a2b9807cdd4: P2 M Ground Theory Heights  Heights Vertical eval spec Rest lin 0a2b9807cdd4
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical eval spec Rest lin 0a2b9807cdd4 construction uses the P2 M Ground Theory Heights  Heights Vertical eval spec Rest lin 0a2b9807cdd4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormIdentity.lean#L48-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormIdentity.lean#L48-L62

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_eval_specRest_lin_0a2b9807cdd4 (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) (u : Fin n → 𝓞 K) :
    eval (fun j => kToFrac K e n (algebraMap (𝓞 K) K (u j)))
        (specRest (kToFrac K e n) (g.map (algebraMap (𝓞 K) K)) (parYF K e n)) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (rename Sum.inl (specFirst g u)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«eval_specRest_lin» := P2M_GroundTheory_Heights__Heights_Vertical_eval_specRest_lin_0a2b9807cdd4
