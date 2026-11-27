-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Krd_DC_densG
-- name    : PositivityTheory.SiegelWeilFormula.Krd.DC.densG
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:56:44.030801+00:00
-- url     : https://prove2.me/theorems/d7efac0f-5692-59d2-8edf-91f12a188d87
-- title:
--   DC: dens G
-- statement:
--   The DC construction uses the dens G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/CayleyTransform/DenseC.lean#L100-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/CayleyTransform/DenseC.lean#L100-L114

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseCP
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseC
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

theorem PositivityTheory.SiegelWeilFormula.Krd.DC.densG {J : Matrix ι ι ℂ} {c d : ℂ} (hc : Jᴴ = c • J) (hcc : c * c = 1) (hd : J * J = d • 1) (hd0 : d ≠ 0)
    (hds : star d = d) {S : Set (Matrix ι ι ℂ)} (hS : Dense S) (hSp : ∀ X ∈ S, proj J d X ∈ S)
    (hSc : ∀ X ∈ S, IsUnit (1 - X).det → cay X ∈ S) {V : Set (Matrix ι ι ℂ)} (hV : IsOpen V) {h : Matrix ι ι ℂ}
    (hhV : h ∈ V) (hh : InU J h) : ∃ h' ∈ V, h' ∈ S ∧ InU J h' := by sorry
