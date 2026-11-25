-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_sum_sign_prod_ell
-- name    : PositivityTheory.Rg.Sw.LVs.STD.sum_sign_prod_ell
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:24.4955+00:00
-- url     : https://prove2.me/theorems/433404a3-ca7e-44b0-a12b-34cae74e9961
-- title:
--   STD: sum sign prod ell
-- statement:
--   The STD construction uses the sum sign prod ell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SingToDiff.lean#L55-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SingToDiff.lean#L55-L69

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
open PositivityTheory.Rg.Sw.LVs.STD
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.STD.sum_sign_prod_ell (β : Matrix (Fin n) (Fin n) ℂ) :
    ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
      ((List.ofFn (ml σ)).map fun a => ell β (Matrix.single a.1 a.2 1)).prod =
      (2 * Real.pi * Complex.I) ^ Fintype.card (Fin n) * β.det := by sorry
