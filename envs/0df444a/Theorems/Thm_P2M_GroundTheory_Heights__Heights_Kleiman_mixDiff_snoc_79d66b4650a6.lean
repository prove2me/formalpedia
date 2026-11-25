-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mixDiff_snoc_79d66b4650a6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mixDiff_snoc_79d66b4650a6
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:24:14.419902+00:00
-- url     : https://prove2.me/theorems/588dcc15-eac7-4b70-aa43-8322fba1a5a0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mix Diff snoc 79d66b4650a6: P2 M Ground Theory Heights  Heights Kleiman mix Diff snoc 79d66b4650a6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mix Diff snoc 79d66b4650a6 construction uses the P2 M Ground Theory Heights  Heights Kleiman mix Diff snoc 79d66b4650a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumAdditive.lean#L76-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumAdditive.lean#L76-L92

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mixDiff_snoc_79d66b4650a6 (f : G → ℤ) {m : ℕ} (L : Fin m → G) (X : G) :
    mixDiff f (Fin.snoc (α := fun _ => G) L X) = mixDiff (fun g => f (X * g)) L - mixDiff f L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mixDiff_snoc» := P2M_GroundTheory_Heights__Heights_Kleiman_mixDiff_snoc_79d66b4650a6
