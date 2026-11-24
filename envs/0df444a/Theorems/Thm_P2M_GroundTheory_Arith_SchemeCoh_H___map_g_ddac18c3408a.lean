-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_H___map_g_ddac18c3408a
-- name    : P2M_GroundTheory_Arith_SchemeCoh_H___map_g_ddac18c3408a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:48.357054+00:00
-- url     : https://prove2.me/theorems/64f622e2-acda-4319-b5ef-186a323aa28f
-- title:
--   P2 M Ground Theory Arith Scheme Coh H   map g ddac18c3408a: P2 M Ground Theory Arith Scheme Coh H   map g ddac18c3408a
-- statement:
--   The P2 M Ground Theory Arith Scheme Coh H   map g ddac18c3408a construction uses the P2 M Ground Theory Arith Scheme Coh H   map g ddac18c3408a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L193-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L193-L196

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

theorem P2M_GroundTheory_Arith_SchemeCoh_H___map_g_ddac18c3408a {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : Sheaf.H S.X₂ n₀) :
    H.δ hS n₀ n₁ h (Sheaf.H.map S.g n₀ x) = 0 := by sorry

alias «GroundTheory».«Arith».«SchemeCoh».«H».«δ_map_g» := P2M_GroundTheory_Arith_SchemeCoh_H___map_g_ddac18c3408a
