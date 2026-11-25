-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_vertComps_finite__2f6383468a96
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_vertComps_finite__2f6383468a96
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:43:47.104373+00:00
-- url     : https://prove2.me/theorems/137741b1-cb99-48c9-afed-a3cb8f1b2e5f
-- title:
--   P2 M Ground Theory Heights  Heights Vertical vert Comps finite  2f6383468a96: P2 M Ground Theory Heights  Heights Vertical vert Comps finite  2f6383468a96
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical vert Comps finite  2f6383468a96 construction uses the P2 M Ground Theory Heights  Heights Vertical vert Comps finite  2f6383468a96 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/POrdEq.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/POrdEq.lean#L15-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_POrdEq
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

theorem P2M_GroundTheory_Heights__Heights_Vertical_vertComps_finite__2f6383468a96 {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)) :
    (vertComps I u v).Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«vertComps_finite'» := P2M_GroundTheory_Heights__Heights_Vertical_vertComps_finite__2f6383468a96
