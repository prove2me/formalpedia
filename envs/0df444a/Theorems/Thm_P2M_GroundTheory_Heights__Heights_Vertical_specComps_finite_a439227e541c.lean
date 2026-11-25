-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_specComps_finite_a439227e541c
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_specComps_finite_a439227e541c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:43:22.4438+00:00
-- url     : https://prove2.me/theorems/7a583185-cbab-4c89-b1fb-efd25d2fe484
-- title:
--   P2 M Ground Theory Heights  Heights Vertical spec Comps finite a439227e541c: P2 M Ground Theory Heights  Heights Vertical spec Comps finite a439227e541c
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical spec Comps finite a439227e541c construction uses the P2 M Ground Theory Heights  Heights Vertical spec Comps finite a439227e541c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/POrdEq.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/POrdEq.lean#L11-L13

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_specComps_finite_a439227e541c {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) : (specComps I v).Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«specComps_finite» := P2M_GroundTheory_Heights__Heights_Vertical_specComps_finite_a439227e541c
