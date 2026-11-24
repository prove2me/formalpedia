-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Asm_aeval_prod_linear_factors
-- name    : PositivityTheory.RgUd.T.Nil.Asm.aeval_prod_linear_factors
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:03.17194+00:00
-- url     : https://prove2.me/theorems/29867bf9-e48d-415c-a099-858d15094aa3
-- title:
--   Asm: aeval prod linear factors
-- statement:
--   The Asm construction uses the aeval prod linear factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/NilpotentHypotheses/AevalProdLinearFactors.lean#L67-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/NilpotentHypotheses/AevalProdLinearFactors.lean#L67-L76

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

theorem PositivityTheory.RgUd.T.Nil.Asm.aeval_prod_linear_factors (R : Module.End ℂ M) (β : ℂ) (γ : ℝ → ℂ) (a : List ℝ) :
    aeval R ((a.map fun x => C β - C (γ x) * X).prod) =
      ((a.map fun x => β • LinearMap.id - γ x • R).prod : Module.End ℂ M) := by sorry
