-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_chowDegree_eq_573b7e6f4160
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_chowDegree_eq_573b7e6f4160
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:13:29.399078+00:00
-- url     : https://prove2.me/theorems/8242b25c-8acd-4954-aa29-837a3e55320d
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow chow Degree eq 573b7e6f4160: P2 M Ground Theory Heights  Heights Objects Chow chow Degree eq 573b7e6f4160
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow chow Degree eq 573b7e6f4160 construction uses the P2 M Ground Theory Heights  Heights Objects Chow chow Degree eq 573b7e6f4160 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L88-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L88-L103

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_chowDegree_eq_573b7e6f4160 {F : Type*} [Field F] {I : Ideal (MvPolynomial (Fin n) F)} {k δ : ℕ}
    (hk : 0 < k) {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f)
    (hδ : IsMultiHomog δ f) : chowDegree I k = δ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«chowDegree_eq» := P2M_GroundTheory_Heights__Heights_ObjectsChow_chowDegree_eq_573b7e6f4160
