-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_li_basis
-- name    : ReciprocityTheory.ReducedBases.T2.li_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:01.505695+00:00
-- url     : https://prove2.me/theorems/175dba9c-c30c-4ffd-a8c4-4a3cdbe6fac8
-- title:
--   T2: li basis
-- statement:
--   The T2 construction uses the li basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/TBInjective.lean#L123-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/TBInjective.lean#L123-L144

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
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

theorem ReciprocityTheory.ReducedBases.T2.li_basis (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hAB : A = Bᴴ * B)
    (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) :
    LinearIndependent ℝ (fun i => fB 1 (e i)) ∧ LinearIndependent ℝ (fun i => fB B (e i)) := by sorry
