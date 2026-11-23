-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_IsShortForm_a__ne_zero_or_a__ne_zero_4cc4d6e7c199
-- name    : P2M_GroundTheory_Global_IsShortForm_a__ne_zero_or_a__ne_zero_4cc4d6e7c199
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:43.815893+00:00
-- url     : https://prove2.me/theorems/fdde3b6e-02d0-42da-89df-bc88458614bb
-- title:
--   P2 M Ground Theory Global Is Short Form a  ne zero or a  ne zero 4cc4d6e7c199: P2 M Ground Theory Global Is Short Form a  ne zero or a  ne zero 4cc4d6e7c199
-- statement:
--   The P2 M Ground Theory Global Is Short Form a  ne zero or a  ne zero 4cc4d6e7c199 construction uses the P2 M Ground Theory Global Is Short Form a  ne zero or a  ne zero 4cc4d6e7c199 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunction.lean#L36-L42

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

theorem P2M_GroundTheory_Global_IsShortForm_a__ne_zero_or_a__ne_zero_4cc4d6e7c199 {W : WeierstrassCurve F} [W.IsElliptic]
    (hW : IsShortForm W) : W.a₄ ≠ 0 ∨ W.a₆ ≠ 0 := by sorry

alias «GroundTheory».«Global».«IsShortForm».«a₄_ne_zero_or_a₆_ne_zero» := P2M_GroundTheory_Global_IsShortForm_a__ne_zero_or_a__ne_zero_4cc4d6e7c199
