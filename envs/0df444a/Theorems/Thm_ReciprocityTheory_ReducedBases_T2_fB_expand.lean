-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_fB_expand
-- name    : ReciprocityTheory.ReducedBases.T2.fB_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:51.668799+00:00
-- url     : https://prove2.me/theorems/2359022a-a281-43b3-aadb-72bf82303956
-- title:
--   T2: f B expand
-- statement:
--   The T2 construction uses the f B expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/TBInjective.lean#L99-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/TBInjective.lean#L99-L104

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

theorem ReciprocityTheory.ReducedBases.T2.fB_expand (B : Matrix (Fin d) (Fin d) ℝ) (e : Module.Basis (Fin d) ℤ (Fin d → ℤ))
    (x : Fin d → ℤ) : fB B x = ∑ i, ((e.repr x i : ℤ) : ℝ) • fB B (e i) := by sorry
