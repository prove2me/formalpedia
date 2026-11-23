-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_detD_fin
-- name    : PositivityTheory.Rg.Sw.LVs.CK.detD_fin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:11.632056+00:00
-- url     : https://prove2.me/theorems/3c0bbaae-ef8e-4956-b024-2f9f43413739
-- title:
--   CK: det D fin
-- statement:
--   The CK construction uses the det D fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetDFin.lean#L36-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetDFin.lean#L36-L47

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

theorem PositivityTheory.Rg.Sw.LVs.CK.detD_fin (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ → ℂ) (hG : AnalyticAt ℂ G 0) :
    detD G = ∑ σ : Equiv.Perm (Fin N), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ N G 0 (fun k => Matrix.single k (σ k) 1) := by sorry
