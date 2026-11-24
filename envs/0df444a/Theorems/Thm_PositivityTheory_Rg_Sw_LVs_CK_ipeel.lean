-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_ipeel
-- name    : PositivityTheory.Rg.Sw.LVs.CK.ipeel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:18.311507+00:00
-- url     : https://prove2.me/theorems/1df3940c-b83e-4ce5-bab0-438845003c57
-- title:
--   CK: ipeel
-- statement:
--   The CK construction uses the ipeel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetDFin.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetDFin.lean#L31-L34

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDet
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetDFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem PositivityTheory.Rg.Sw.LVs.CK.ipeel (G : F → ℂ) (x : F) (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin (n + 1) → F) (i0 : Fin (n + 1)) :
    iteratedFDeriv ℂ (n + 1) G x u = iteratedFDeriv ℂ n (fun y => fderiv ℂ G y (u i0)) x (fun k => u (i0.succAbove k)) := by sorry
