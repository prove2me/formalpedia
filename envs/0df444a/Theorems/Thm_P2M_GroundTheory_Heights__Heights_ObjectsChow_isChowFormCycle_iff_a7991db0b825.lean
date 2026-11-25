-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isChowFormCycle_iff_a7991db0b825
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_isChowFormCycle_iff_a7991db0b825
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:13:46.723488+00:00
-- url     : https://prove2.me/theorems/1afdaa7e-137e-4330-bf55-226b73f335b0
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow is Chow Form Cycle iff a7991db0b825: P2 M Ground Theory Heights  Heights Objects Chow is Chow Form Cycle iff a7991db0b825
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow is Chow Form Cycle iff a7991db0b825 construction uses the P2 M Ground Theory Heights  Heights Objects Chow is Chow Form Cycle iff a7991db0b825 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L75-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L75-L79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_isChowFormCycle_iff_a7991db0b825 {F : Type*} [Field F] {k : ℕ} (Z : ProjCycle F n)
    (f : MvPolynomial (Fin k × Fin n) F) :
    IsChowFormCycle Z k f ↔ ∃ c : F, c ≠ 0 ∧ ∃ g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin k × Fin n) F,
      (∀ W ∈ Z.support, IsChowForm W k (g W)) ∧ f = C c * IndefiniteRowSideFullHecke.ArithBezout.cycleChowForm Z g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«isChowFormCycle_iff» := P2M_GroundTheory_Heights__Heights_ObjectsChow_isChowFormCycle_iff_a7991db0b825
