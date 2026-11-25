-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_dK_xZx
-- name    : PositivityTheory.Rg.Sw.LVs.II.dK_xZx
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:40.618801+00:00
-- url     : https://prove2.me/theorems/79817319-834b-4cfe-af64-e0bbdd8f2df8
-- title:
--   II: d K x Zx
-- statement:
--   The II construction uses the d K x Zx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivXZxSkew.lean#L79-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivXZxSkew.lean#L79-L85

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

theorem PositivityTheory.Rg.Sw.LVs.II.dK_xZx (Z x e : M2 n) (i j : Fin n ⊕ Fin n) :
    dK (fun y : M2 n => (y * Z * yᴴ) i j) x e = (e * (x * Z * xᴴ) - (x * Z * xᴴ) * e) i j := by sorry
