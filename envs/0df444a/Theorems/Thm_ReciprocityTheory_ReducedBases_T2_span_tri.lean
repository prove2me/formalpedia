-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_span_tri
-- name    : ReciprocityTheory.ReducedBases.T2.span_tri
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:09:58.648469+00:00
-- url     : https://prove2.me/theorems/89b9e6d4-25ed-471f-88b2-ef5d334c53b6
-- title:
--   T2: span tri
-- statement:
--   The T2 construction uses the span tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/SizeReduce.lean#L9-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/SizeReduce.lean#L9-L38

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_SizeReduce
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Submodule

theorem ReciprocityTheory.ReducedBases.T2.span_tri {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {d : ℕ} (v : Fin d → M)
    (W : Fin d → Fin d → R) (hW : ∀ i l, i ≤ l → W i l = 0) (S : Set (Fin d))
    (hS : ∀ i ∈ S, ∀ l < i, l ∈ S) :
    span R (v '' S) = span R ((fun i => v i - ∑ l, W i l • v l) '' S) := by sorry
