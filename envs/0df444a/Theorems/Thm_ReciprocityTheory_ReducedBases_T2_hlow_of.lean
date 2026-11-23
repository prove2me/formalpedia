-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_hlow_of
-- name    : ReciprocityTheory.ReducedBases.T2.hlow_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:33:32.088014+00:00
-- url     : https://prove2.me/theorems/2c27bab4-a6ed-488d-867a-0de211132c46
-- title:
--   T2: hlow of
-- statement:
--   The T2 construction uses the hlow of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/PrefixProdGeOne.lean#L73-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/PrefixProdGeOne.lean#L73-L115

import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
import Definitions.Def_ReciprocityTheory_ReducedBases_PrefixProdGeOne
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
open Finset InnerProductSpace Matrix
variable {d : ℕ}

theorem ReciprocityTheory.ReducedBases.T2.hlow_of (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hAB : A = Bᴴ * B) :
    ∃ c : ℝ, 0 < c ∧ ∀ (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (k : Fin d),
      c ≤ ∏ j ∈ univ.filter (fun j : Fin d => j ≤ k), ‖gs (fun i => fB B (e i)) j‖ ^ 2 := by sorry
