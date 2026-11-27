-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_H_exact__8bc15c0024ca
-- name    : P2M_GroundTheory_Arith_SchemeCoh_H_exact__8bc15c0024ca
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:21.471316+00:00
-- url     : https://prove2.me/theorems/55ee289c-2830-5d32-ba00-5fa5ba3a45a5
-- title:
--   P2 M Ground Theory Arith Scheme Coh H exact  8bc15c0024ca: P2 M Ground Theory Arith Scheme Coh H exact  8bc15c0024ca
-- statement:
--   The P2 M Ground Theory Arith Scheme Coh H exact  8bc15c0024ca construction uses the P2 M Ground Theory Arith Scheme Coh H exact  8bc15c0024ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L177-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L177-L179

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
include hS

theorem P2M_GroundTheory_Arith_SchemeCoh_H_exact__8bc15c0024ca {n : ℕ} (y : Sheaf.H S.X₂ n) (hy : Sheaf.H.map S.g n y = 0) :
    ∃ x : Sheaf.H S.X₁ n, Sheaf.H.map S.f n x = y := by sorry

alias «GroundTheory».«Arith».«SchemeCoh».«H».«exact₂» := P2M_GroundTheory_Arith_SchemeCoh_H_exact__8bc15c0024ca
