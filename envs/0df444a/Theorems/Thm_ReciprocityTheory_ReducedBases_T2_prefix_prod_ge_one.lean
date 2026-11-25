-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_prefix_prod_ge_one
-- name    : ReciprocityTheory.ReducedBases.T2.prefix_prod_ge_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:10:05.372002+00:00
-- url     : https://prove2.me/theorems/c7b9f8b6-68cb-4ca7-b890-3dd1bc75bdbd
-- title:
--   T2: prefix prod ge one
-- statement:
--   The T2 construction uses the prefix prod ge one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/PrefixProdGeOne.lean#L11-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/PrefixProdGeOne.lean#L11-L71

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

theorem ReciprocityTheory.ReducedBases.T2.prefix_prod_ge_one (e : Module.Basis (Fin d) ℤ (Fin d → ℤ))
    (hU : LinearIndependent ℝ (fun i => fB 1 (e i))) (k : Fin d) :
    1 ≤ ∏ j ∈ univ.filter (fun j : Fin d => j ≤ k), ‖gs (fun i => fB 1 (e i)) j‖ ^ 2 := by sorry
