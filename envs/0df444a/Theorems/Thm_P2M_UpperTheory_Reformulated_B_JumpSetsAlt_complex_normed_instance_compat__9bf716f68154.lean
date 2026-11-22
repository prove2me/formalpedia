-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_JumpSetsAlt_complex_normed_instance_compat__9bf716f68154
-- name    : P2M_UpperTheory_Reformulated_B_JumpSetsAlt_complex_normed_instance_compat__9bf716f68154
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:03:03.572013+00:00
-- url     : https://prove2.me/theorems/b0572871-4198-47d6-a8d8-501f6dfdb039
-- title:
--   P2 M Upper Theory Reformulated B Jump Sets Alt complex normed instance compat  9bf716f68154: P2 M Upper Theory Reformulated B Jump Sets Alt complex normed instance compat  9bf716f68154
-- statement:
--   The P2 M Upper Theory Reformulated B Jump Sets Alt complex normed instance compat  9bf716f68154 construction uses the P2 M Upper Theory Reformulated B Jump Sets Alt complex normed instance compat  9bf716f68154 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/JumpSets.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/JumpSets.lean#L73-L76

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

theorem P2M_UpperTheory_Reformulated_B_JumpSetsAlt_complex_normed_instance_compat__9bf716f68154.{u_1} :
    ∀ {L : Type u_1} [inst : Field L] [inst_1 : Algebra ℚ L] (ζ a b : L), ζ + ζ⁻¹ ∈ UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b := by sorry

alias «UpperTheory».«Reformulated».«B».«JumpSetsAlt».«complex_normed_instance_compat» := P2M_UpperTheory_Reformulated_B_JumpSetsAlt_complex_normed_instance_compat__9bf716f68154
