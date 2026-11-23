-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CEq_symm_perm
-- name    : PositivityTheory.Rg.Sw.LVs.CEq.symm_perm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:27.14984+00:00
-- url     : https://prove2.me/theorems/b4d497fd-499f-4fee-9507-12758ee2db2e
-- title:
--   CEq: symm perm
-- statement:
--   The CEq construction uses the symm perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/CayleyEq.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/CayleyEq.lean#L36-L38

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [DecidableEq κ]

theorem PositivityTheory.Rg.Sw.LVs.CEq.symm_perm (F : Matrix κ κ ℂ → ℂ) (hF : AnalyticAt ℂ F 0) {n : ℕ} (v : Fin n → Matrix κ κ ℂ)
    (π : Equiv.Perm (Fin n)) : iteratedFDeriv ℂ n F 0 (v ∘ π) = iteratedFDeriv ℂ n F 0 v := by sorry
