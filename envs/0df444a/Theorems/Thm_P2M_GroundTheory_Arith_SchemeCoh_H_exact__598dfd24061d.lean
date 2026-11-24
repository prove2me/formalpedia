-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_H_exact__598dfd24061d
-- name    : P2M_GroundTheory_Arith_SchemeCoh_H_exact__598dfd24061d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:25.547855+00:00
-- url     : https://prove2.me/theorems/78530d29-169e-40b2-8e35-8fa76f121551
-- title:
--   P2 M Ground Theory Arith Scheme Coh H exact  598dfd24061d: P2 M Ground Theory Arith Scheme Coh H exact  598dfd24061d
-- statement:
--   The P2 M Ground Theory Arith Scheme Coh H exact  598dfd24061d construction uses the P2 M Ground Theory Arith Scheme Coh H exact  598dfd24061d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L181-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L181-L183

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

theorem P2M_GroundTheory_Arith_SchemeCoh_H_exact__598dfd24061d {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (y : Sheaf.H S.X₃ n₀)
    (hy : H.δ hS n₀ n₁ h y = 0) : ∃ x : Sheaf.H S.X₂ n₀, Sheaf.H.map S.g n₀ x = y := by sorry

alias «GroundTheory».«Arith».«SchemeCoh».«H».«exact₃» := P2M_GroundTheory_Arith_SchemeCoh_H_exact__598dfd24061d
