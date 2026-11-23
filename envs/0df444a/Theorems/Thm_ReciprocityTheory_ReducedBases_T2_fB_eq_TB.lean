-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_fB_eq_TB
-- name    : ReciprocityTheory.ReducedBases.T2.fB_eq_TB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:52.678436+00:00
-- url     : https://prove2.me/theorems/c2183d5f-e84b-425f-9690-87de173b7c7d
-- title:
--   T2: f B eq TB
-- statement:
--   The T2 construction uses the f B eq TB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/TBInjective.lean#L85-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/TBInjective.lean#L85-L86

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

theorem ReciprocityTheory.ReducedBases.T2.fB_eq_TB (B : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℤ) : fB B x = TB B (fB 1 x) := by sorry
