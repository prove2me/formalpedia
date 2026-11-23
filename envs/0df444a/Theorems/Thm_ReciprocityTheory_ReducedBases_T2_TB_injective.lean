-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_TB_injective
-- name    : ReciprocityTheory.ReducedBases.T2.TB_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:48.366164+00:00
-- url     : https://prove2.me/theorems/eda9ff86-9145-4799-9a08-a848d223c470
-- title:
--   T2: TB injective
-- statement:
--   The T2 construction uses the TB injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/TBInjective.lean#L106-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/TBInjective.lean#L106-L121

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

theorem ReciprocityTheory.ReducedBases.T2.TB_injective (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hAB : A = Bᴴ * B) :
    Function.Injective (TB B) := by sorry
