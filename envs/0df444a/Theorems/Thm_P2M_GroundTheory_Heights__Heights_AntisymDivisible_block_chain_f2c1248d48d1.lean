-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_block_chain_f2c1248d48d1
-- name    : P2M_GroundTheory_Heights__Heights_AntisymDivisible_block_chain_f2c1248d48d1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:44.887138+00:00
-- url     : https://prove2.me/theorems/c93ad79a-5de9-4fc1-803a-a8fc8889b86c
-- title:
--   P2 M Ground Theory Heights  Heights Antisym Divisible block chain f2c1248d48d1: P2 M Ground Theory Heights  Heights Antisym Divisible block chain f2c1248d48d1
-- statement:
--   The P2 M Ground Theory Heights  Heights Antisym Divisible block chain f2c1248d48d1 construction uses the P2 M Ground Theory Heights  Heights Antisym Divisible block chain f2c1248d48d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L176-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L176-L192

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible
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
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymDivisible

theorem P2M_GroundTheory_Heights__Heights_AntisymDivisible_block_chain_f2c1248d48d1 {N j : ℕ} (R : Fin N → Fin N → Prop)
    (hadj : ∀ a b : Fin N, b.val = a.val + 1 → (b.val < j ∨ j ≤ a.val) → R a b)
    (hstep : ∀ a c b : Fin N, a.val < c.val → c.val + 1 = b.val → (b.val < j ∨ j ≤ a.val) →
      R a c → R c b → R a b) :
    ∀ a b : Fin N, a.val < b.val → (b.val < j ∨ j ≤ a.val) → R a b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AntisymDivisible».«block_chain» := P2M_GroundTheory_Heights__Heights_AntisymDivisible_block_chain_f2c1248d48d1
