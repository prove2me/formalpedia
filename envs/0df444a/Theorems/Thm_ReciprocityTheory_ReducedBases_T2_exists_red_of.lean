-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_exists_red_of
-- name    : ReciprocityTheory.ReducedBases.T2.exists_red_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:33:32.223798+00:00
-- url     : https://prove2.me/theorems/ecc9e2ac-f999-4b30-a4c7-e32d9ecd8e09
-- title:
--   T2: exists red of
-- statement:
--   The T2 construction uses the exists red of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/ExistsRedOf.lean#L10-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/ExistsRedOf.lean#L10-L61

import Definitions.Def_ReciprocityTheory_ReducedBases_SizeReduce
import Definitions.Def_ReciprocityTheory_ReducedBases_NormGsoCompSwapRightSqMul
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsRedOf
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
open Finset InnerProductSpace

theorem ReciprocityTheory.ReducedBases.T2.exists_red_of {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (f : (Fin d → ℤ) →ₗ[ℤ] E)
    (hli : ∀ e : Module.Basis (Fin d) ℤ (Fin d → ℤ), LinearIndependent ℝ (fun i => f (e i)))
    (hlow : ∃ c : ℝ, 0 < c ∧ ∀ (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (k : Fin d),
      c ≤ ∏ j ∈ univ.filter (fun j : Fin d => j ≤ k), ‖gs (fun i => f (e i)) j‖ ^ 2) :
    ∃ e : Module.Basis (Fin d) ℤ (Fin d → ℤ), IsRed (fun i => f (e i)) := by sorry
