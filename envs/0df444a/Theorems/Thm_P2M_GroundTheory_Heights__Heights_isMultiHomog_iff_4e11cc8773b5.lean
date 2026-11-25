-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiHomog_iff_4e11cc8773b5
-- name    : P2M_GroundTheory_Heights__Heights_isMultiHomog_iff_4e11cc8773b5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:58.524093+00:00
-- url     : https://prove2.me/theorems/1006f625-f47e-4348-a803-83415817d344
-- title:
--   P2 M Ground Theory Heights  Heights is Multi Homog iff 4e11cc8773b5: P2 M Ground Theory Heights  Heights is Multi Homog iff 4e11cc8773b5
-- statement:
--   The P2 M Ground Theory Heights  Heights is Multi Homog iff 4e11cc8773b5 construction uses the P2 M Ground Theory Heights  Heights is Multi Homog iff 4e11cc8773b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L166-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L166-L173

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {k n : ℕ}
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_isMultiHomog_iff_4e11cc8773b5 (δ : ℕ) (f : MvPolynomial (Fin k × Fin n) R) :
    IsMultiHomog δ f ↔ ∀ i : Fin k, IsWeightedHomogeneous (inGroup i) f δ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isMultiHomog_iff» := P2M_GroundTheory_Heights__Heights_isMultiHomog_iff_4e11cc8773b5
