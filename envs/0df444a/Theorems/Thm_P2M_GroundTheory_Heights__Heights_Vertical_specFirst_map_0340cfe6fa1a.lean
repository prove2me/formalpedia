-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_specFirst_map_0340cfe6fa1a
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_specFirst_map_0340cfe6fa1a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:43:48.54109+00:00
-- url     : https://prove2.me/theorems/7c69c415-4336-4056-b9fc-1b46c9d58796
-- title:
--   P2 M Ground Theory Heights  Heights Vertical spec First map 0340cfe6fa1a: P2 M Ground Theory Heights  Heights Vertical spec First map 0340cfe6fa1a
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical spec First map 0340cfe6fa1a construction uses the P2 M Ground Theory Heights  Heights Vertical spec First map 0340cfe6fa1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGaussEq.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGaussEq.lean#L28-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGaussEq
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

theorem P2M_GroundTheory_Heights__Heights_Vertical_specFirst_map_0340cfe6fa1a {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) {n k : ℕ}
    (g : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    specFirst (g.map φ) (fun j => φ (u j)) = (specFirst g u).map φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«specFirst_map» := P2M_GroundTheory_Heights__Heights_Vertical_specFirst_map_0340cfe6fa1a
