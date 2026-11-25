-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_fderiv_xZx_skew
-- name    : PositivityTheory.Rg.Sw.LVs.II.fderiv_xZx_skew
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:58:22.208932+00:00
-- url     : https://prove2.me/theorems/089d89ef-3dca-43a1-ace6-396ddd86f78a
-- title:
--   II: fderiv x Zx skew
-- statement:
--   The II construction uses the fderiv x Zx skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivXZxSkew.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivXZxSkew.lean#L73-L77

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivXZxSkew
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.II.fderiv_xZx_skew (Z x E : M2 n) (hE : Eᴴ = -E) (i j : Fin n ⊕ Fin n) :
    fderiv ℝ (fun y : M2 n => (y * Z * yᴴ) i j) x (E * x) = (E * (x * Z * xᴴ) - (x * Z * xᴴ) * E) i j := by sorry
