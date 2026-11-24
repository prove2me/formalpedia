-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_push_zero__4bd36dbeb085
-- name    : P2M_GroundTheory_Arith_SchemeCoh_push_zero__4bd36dbeb085
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:40.846751+00:00
-- url     : https://prove2.me/theorems/2a83f87b-b60c-42f3-8998-a9d6dfa74b1a
-- title:
--   P2 M Ground Theory Arith Scheme Coh push zero  4bd36dbeb085: P2 M Ground Theory Arith Scheme Coh push zero  4bd36dbeb085
-- statement:
--   The P2 M Ground Theory Arith Scheme Coh push zero  4bd36dbeb085 construction uses the P2 M Ground Theory Arith Scheme Coh push zero  4bd36dbeb085 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L115-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L115-L118

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
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
open CategoryTheory Opposite TopologicalSpace
universe w u v
variable {X : TopCat.{u}} {ι : Type w}
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
variable {P}
attribute [local semireducible] inter

theorem P2M_GroundTheory_Arith_SchemeCoh_push_zero__4bd36dbeb085 {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (n : ℕ) (σ : Cochain P U n) :
    push U (0 : P ⟶ P') n σ = 0 := by sorry

alias «GroundTheory».«Arith».«SchemeCoh».«push_zero'» := P2M_GroundTheory_Arith_SchemeCoh_push_zero__4bd36dbeb085
