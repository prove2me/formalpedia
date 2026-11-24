-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Asm_aeval_mem
-- name    : PositivityTheory.RgUd.T.Nil.Asm.aeval_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:00.621366+00:00
-- url     : https://prove2.me/theorems/2eb91c38-a652-44af-8b93-e6899712365a
-- title:
--   Asm: aeval mem
-- statement:
--   The Asm construction uses the aeval mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/NilpotentHypotheses/AevalProdLinearFactors.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/NilpotentHypotheses/AevalProdLinearFactors.lean#L20-L28

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

theorem PositivityTheory.RgUd.T.Nil.Asm.aeval_mem (K : Submodule ℂ M) (R : Module.End ℂ M) (hK : ∀ m ∈ K, R m ∈ K) (p : ℂ[X]) :
    ∀ m ∈ K, (aeval R p) m ∈ K := by sorry
