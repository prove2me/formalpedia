-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_vertComps_finite_caa4eaa24ca7
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_vertComps_finite_caa4eaa24ca7
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:44:08.024801+00:00
-- url     : https://prove2.me/theorems/12a7acc7-b30c-4e21-a33e-28f3fa96df44
-- title:
--   P2 M Ground Theory Heights  Heights Vertical vert Comps finite caa4eaa24ca7: P2 M Ground Theory Heights  Heights Vertical vert Comps finite caa4eaa24ca7
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical vert Comps finite caa4eaa24ca7 construction uses the P2 M Ground Theory Heights  Heights Vertical vert Comps finite caa4eaa24ca7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PVertTermEq.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PVertTermEq.lean#L11-L14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PVertTermEq
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

theorem P2M_GroundTheory_Heights__Heights_Vertical_vertComps_finite_caa4eaa24ca7 {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)) :
    (vertComps I u v).Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«vertComps_finite» := P2M_GroundTheory_Heights__Heights_Vertical_vertComps_finite_caa4eaa24ca7
