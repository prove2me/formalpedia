-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Asm_pow_mul_prod
-- name    : PositivityTheory.RgUd.T.Nil.Asm.pow_mul_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:54.534555+00:00
-- url     : https://prove2.me/theorems/fb2f8496-c5c8-44e7-80c7-73247c89d83e
-- title:
--   Asm: pow mul prod
-- statement:
--   The Asm construction uses the pow mul prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/NilpotentHypotheses/AevalProdLinearFactors.lean#L78-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/NilpotentHypotheses/AevalProdLinearFactors.lean#L78-L91

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

theorem PositivityTheory.RgUd.T.Nil.Asm.pow_mul_prod (R R' : Module.End ℂ M) (hRR : R * R' = 1) (hR'R : R' * R = 1) (β : ℂ) (γ : ℝ → ℂ) :
    ∀ l : List ℝ, R ^ l.length * ((l.map fun x => β • R' - γ x • (1 : Module.End ℂ M)).prod) =
      (l.map fun x => β • (1 : Module.End ℂ M) - γ x • R).prod := by sorry
