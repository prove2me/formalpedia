-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_DC_scalar_avoid
-- name    : PositivityTheory.SiegelWeilFormula.Krd.DC.scalar_avoid
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:03:51.471857+00:00
-- url     : https://prove2.me/theorems/bb89e7c7-702c-56e5-8d53-8123b9637307
-- title:
--   DC: scalar avoid
-- statement:
--   The DC construction uses the scalar avoid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/CayleyTransform/DenseC.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/CayleyTransform/DenseC.lean#L91-L93

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseCP
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseC
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_CP_scalar_avoid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Krd PositivityTheory.SiegelWeilFormula.Krd.DC
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem PositivityTheory.SiegelWeilFormula.Krd.DC.scalar_avoid {J h : Matrix ι ι ℂ} (hh : InU J h) {V : Set (Matrix ι ι ℂ)} (hV : IsOpen V) (hhV : h ∈ V) :
    ∃ μ : ℂ, star μ * μ = 1 ∧ μ • h ∈ V ∧ IsUnit (1 + μ • h).det := by sorry
