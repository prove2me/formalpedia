-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_size_reduce
-- name    : ReciprocityTheory.ReducedBases.T2.size_reduce
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:09:56.313842+00:00
-- url     : https://prove2.me/theorems/07dbf133-c37a-5898-b18a-e14b4242a989
-- title:
--   T2: size reduce
-- statement:
--   The T2 construction uses the size reduce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/SizeReduce.lean#L182-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/SizeReduce.lean#L182-L211

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

theorem ReciprocityTheory.ReducedBases.T2.size_reduce {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (f : (Fin d → ℤ) →ₗ[ℤ] E)
    (hli : ∀ e : Module.Basis (Fin d) ℤ (Fin d → ℤ), LinearIndependent ℝ (fun i => f (e i)))
    (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) :
    ∃ e' : Module.Basis (Fin d) ℤ (Fin d → ℤ), gs (fun i => f (e' i)) = gs (fun i => f (e i)) ∧
      ∀ i j : Fin d, j < i → |mu (fun i => f (e' i)) i j| ≤ 1 / 2 := by sorry
