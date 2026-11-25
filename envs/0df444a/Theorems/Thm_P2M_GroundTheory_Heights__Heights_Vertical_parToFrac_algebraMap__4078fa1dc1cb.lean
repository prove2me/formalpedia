-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_parToFrac_algebraMap__4078fa1dc1cb
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_parToFrac_algebraMap__4078fa1dc1cb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:43:32.904795+00:00
-- url     : https://prove2.me/theorems/6a2ecfd0-503e-48f5-8430-d93efbc785c2
-- title:
--   P2 M Ground Theory Heights  Heights Vertical par To Frac algebra Map  4078fa1dc1cb: P2 M Ground Theory Heights  Heights Vertical par To Frac algebra Map  4078fa1dc1cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical par To Frac algebra Map  4078fa1dc1cb construction uses the P2 M Ground Theory Heights  Heights Vertical par To Frac algebra Map  4078fa1dc1cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormIdentity.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormIdentity.lean#L23-L26

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_parToFrac_algebraMap__4078fa1dc1cb (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (x : MvPolynomial (Par e n) (𝓞 K)) :
    parToFrac e n v (algebraMap _ (ParDVR e n v) x) = algebraMap _ (ParFrac K e n) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«parToFrac_algebraMap'» := P2M_GroundTheory_Heights__Heights_Vertical_parToFrac_algebraMap__4078fa1dc1cb
