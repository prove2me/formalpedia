-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mixDiff_snoc_mul_363364318b58
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mixDiff_snoc_mul_363364318b58
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:03:24.615133+00:00
-- url     : https://prove2.me/theorems/670c8d76-abb4-4042-b671-73f054997c73
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mix Diff snoc mul 363364318b58: P2 M Ground Theory Heights  Heights Kleiman mix Diff snoc mul 363364318b58
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mix Diff snoc mul 363364318b58 construction uses the P2 M Ground Theory Heights  Heights Kleiman mix Diff snoc mul 363364318b58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumAdditive.lean#L94-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumAdditive.lean#L94-L104

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumAdditive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumEventual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterSumTopVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_InterSumEventuallyEqInterNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumAdditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
variable {G : Type*} [CommMonoid G]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mixDiff_snoc_mul_363364318b58 (f : G → ℤ) {m : ℕ} (L : Fin m → G) (X Y : G) :
    mixDiff f (Fin.snoc (α := fun _ => G) L (X * Y)) =
      mixDiff f (Fin.snoc (α := fun _ => G) L X) + mixDiff f (Fin.snoc (α := fun _ => G) L Y) +
        mixDiff f (Fin.snoc (α := fun _ => G) (Fin.snoc (α := fun _ => G) L X) Y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mixDiff_snoc_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_mixDiff_snoc_mul_363364318b58
