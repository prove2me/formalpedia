-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_Det2_v_det_scaled
-- name    : ReciprocityTheory.PGsh.Up.Det2.v_det_scaled
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:36.497096+00:00
-- url     : https://prove2.me/theorems/2a94d192-c477-5eef-bed0-0e0dda3f9f53
-- title:
--   Det2: v det scaled
-- statement:
--   The Det2 construction uses the v det scaled property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FrobEqOfLe.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FrobEqOfLe.lean#L9-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_FrobEqOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Filter Topology
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.Det2

theorem ReciprocityTheory.PGsh.Up.Det2.v_det_scaled {C : Type} [Field C] (v : Valuation C NNReal) {ι : Type} [Fintype ι]
    [DecidableEq ι] (c : Matrix ι ι C) (y z : ι → C) :
    v (Matrix.of fun j k => c j k * (y j / z k)).det =
      v c.det * (∏ j, v (y j)) / ∏ k, v (z k) := by sorry
