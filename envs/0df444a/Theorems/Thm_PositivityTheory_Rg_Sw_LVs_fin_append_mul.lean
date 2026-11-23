-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_fin_append_mul
-- name    : PositivityTheory.Rg.Sw.LVs.fin_append_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:28.91387+00:00
-- url     : https://prove2.me/theorems/645ddec4-6cfb-4be8-a42e-cc7c0059f558
-- title:
--   LVs: fin append mul
-- statement:
--   The LVs construction uses the fin append mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IteratedFDerivMulConstOf.lean#L129-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IteratedFDerivMulConstOf.lean#L129-L131

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.fin_append_mul {a b : ℕ} (M : M2 n) (u : Fin a → M2 n) (v : Fin b → M2 n) :
    (fun i => M * Fin.append u v i) = Fin.append (fun i => M * u i) (fun i => M * v i) := by sorry
