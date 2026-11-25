-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_H_map_f___5f0aedcbf060
-- name    : P2M_GroundTheory_Arith_SchemeCoh_H_map_f___5f0aedcbf060
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:24.806414+00:00
-- url     : https://prove2.me/theorems/51e8e57a-5a4a-5470-b248-8e4fa60ce700
-- title:
--   P2 M Ground Theory Arith Scheme Coh H map f   5f0aedcbf060: P2 M Ground Theory Arith Scheme Coh H map f   5f0aedcbf060
-- statement:
--   The P2 M Ground Theory Arith Scheme Coh H map f   5f0aedcbf060 construction uses the P2 M Ground Theory Arith Scheme Coh H map f   5f0aedcbf060 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L198-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L198-L201

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Limits Opposite Abelian
universe w' v u
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)

theorem P2M_GroundTheory_Arith_SchemeCoh_H_map_f___5f0aedcbf060 {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : Sheaf.H S.X₃ n₀) :
    Sheaf.H.map S.f n₁ (H.δ hS n₀ n₁ h x) = 0 := by sorry

alias «GroundTheory».«Arith».«SchemeCoh».«H».«map_f_δ» := P2M_GroundTheory_Arith_SchemeCoh_H_map_f___5f0aedcbf060
