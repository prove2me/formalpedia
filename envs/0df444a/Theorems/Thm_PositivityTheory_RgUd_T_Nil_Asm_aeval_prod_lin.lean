-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Asm_aeval_prod_lin
-- name    : PositivityTheory.RgUd.T.Nil.Asm.aeval_prod_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:15.140798+00:00
-- url     : https://prove2.me/theorems/a0e308c5-5477-4732-b517-525932327b19
-- title:
--   Asm: aeval prod lin
-- statement:
--   The Asm construction uses the aeval prod lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/NilpotentHypotheses/AevalProdLinearFactors.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/NilpotentHypotheses/AevalProdLinearFactors.lean#L60-L65

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_NilpotentHypotheses_AevalProdLinearFactors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Asm
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.RgUd.T.Nil.Asm.aeval_prod_lin (R : Module.End ℂ M) (α : ℝ → ℂ) (a : List ℝ) :
    aeval R ((a.map fun x => X - C (α x)).prod) = ((a.map fun x => R - α x • LinearMap.id).prod : Module.End ℂ M) := by sorry
