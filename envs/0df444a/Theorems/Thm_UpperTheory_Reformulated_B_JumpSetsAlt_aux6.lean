-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_JumpSetsAlt_aux6
-- name    : UpperTheory.Reformulated.B.JumpSetsAlt.aux6
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:33.741281+00:00
-- url     : https://prove2.me/theorems/c5b1237c-e6f2-409e-9897-40d9610a29da
-- title:
--   Jump Sets Alt: aux6
-- statement:
--   The Jump Sets Alt construction uses the aux6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/JumpSets.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/JumpSets.lean#L27-L30

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_JumpSets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold
open scoped Classical

theorem UpperTheory.Reformulated.B.JumpSetsAlt.aux6 :
    ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L), CharZero ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) := by sorry
