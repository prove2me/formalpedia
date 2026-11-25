-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_eulerChar_eq_finrank_H0_8f9d9dde05af
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_eulerChar_eq_finrank_H0_8f9d9dde05af
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:01:55.9738+00:00
-- url     : https://prove2.me/theorems/29523fe1-77ee-410a-b927-e13fed296f5e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman euler Char eq finrank H0 8f9d9dde05af: P2 M Ground Theory Heights  Heights Kleiman euler Char eq finrank H0 8f9d9dde05af
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman euler Char eq finrank H0 8f9d9dde05af construction uses the P2 M Ground Theory Heights  Heights Kleiman euler Char eq finrank H0 8f9d9dde05af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleSnapper.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleSnapper.lean#L15-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleSnapperSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsMemSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleSnapper
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_eulerChar_eq_finrank_H0_8f9d9dde05af {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (F : SubSystem k x Ω) (hF : ∀ i, 1 ≤ i → Subsingleton (F.H i)) :
    eulerChar k F = Module.finrank k (F.H 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«eulerChar_eq_finrank_H0» := P2M_GroundTheory_Heights__Heights_Kleiman_eulerChar_eq_finrank_H0_8f9d9dde05af
