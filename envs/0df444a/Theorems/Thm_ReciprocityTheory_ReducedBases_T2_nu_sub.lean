-- Prove2me | Theorems.Thm_ReciprocityTheory_ReducedBases_T2_nu_sub
-- name    : ReciprocityTheory.ReducedBases.T2.nu_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:33:35.743645+00:00
-- url     : https://prove2.me/theorems/ea28e6e9-f965-4fa4-a7d5-0d3187ad84fd
-- title:
--   T2: nu sub
-- statement:
--   The T2 construction uses the nu sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/LatticeReduction.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/LatticeReduction.lean#L16-L18

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsBoundedBasis
import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

theorem ReciprocityTheory.ReducedBases.T2.nu_sub (b : Fin d → E) (c w : Fin d → ℝ) (N : ℝ) (j : Fin d) :
    nu b (fun l => c l - N * w l) j = nu b c j - N * nu b w j := by sorry
