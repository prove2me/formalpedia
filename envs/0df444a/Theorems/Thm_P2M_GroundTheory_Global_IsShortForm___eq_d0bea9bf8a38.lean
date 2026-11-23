-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_IsShortForm___eq_d0bea9bf8a38
-- name    : P2M_GroundTheory_Global_IsShortForm___eq_d0bea9bf8a38
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:57.360468+00:00
-- url     : https://prove2.me/theorems/b520de68-bef0-4ab9-9ab1-c4487ec80761
-- title:
--   P2 M Ground Theory Global Is Short Form   eq d0bea9bf8a38: P2 M Ground Theory Global Is Short Form   eq d0bea9bf8a38
-- statement:
--   The P2 M Ground Theory Global Is Short Form   eq d0bea9bf8a38 construction uses the P2 M Ground Theory Global Is Short Form   eq d0bea9bf8a38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L26-L29

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open WeierstrassCurve OnePoint
variable {F : Type*} [Field F]
open ShortWeierstrass

theorem P2M_GroundTheory_Global_IsShortForm___eq_d0bea9bf8a38 {W : WeierstrassCurve F} (hW : IsShortForm W) :
    W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := by sorry

alias «GroundTheory».«Global».«IsShortForm».«Δ_eq» := P2M_GroundTheory_Global_IsShortForm___eq_d0bea9bf8a38
