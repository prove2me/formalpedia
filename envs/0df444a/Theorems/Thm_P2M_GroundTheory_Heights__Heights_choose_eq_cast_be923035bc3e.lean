-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_choose_eq_cast_be923035bc3e
-- name    : P2M_GroundTheory_Heights__Heights_choose_eq_cast_be923035bc3e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:49.825278+00:00
-- url     : https://prove2.me/theorems/0579f547-3660-4bc6-a565-7142130ee7f4
-- title:
--   P2 M Ground Theory Heights  Heights choose eq cast be923035bc3e: P2 M Ground Theory Heights  Heights choose eq cast be923035bc3e
-- statement:
--   The P2 M Ground Theory Heights  Heights choose eq cast be923035bc3e construction uses the P2 M Ground Theory Heights  Heights choose eq cast be923035bc3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L167-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L167-L173

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_choose_eq_cast_be923035bc3e {α β : Type} (e : α = β) {p : α → Prop} {q : β → Prop}
    (hp : ∃ x, p x) (hq : ∃ y, q y) (hpq : ∀ x, q (cast e x) ↔ p x) :
    Classical.choose hq = cast e (Classical.choose hp) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«choose_eq_cast» := P2M_GroundTheory_Heights__Heights_choose_eq_cast_be923035bc3e
