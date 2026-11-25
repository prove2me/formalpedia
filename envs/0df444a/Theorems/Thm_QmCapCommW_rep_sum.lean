-- Prove2me | Theorems.Thm_QmCapCommW_rep_sum
-- name    : QmCapCommW.rep_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:05:57.811779+00:00
-- url     : https://prove2.me/theorems/060842ff-4953-46c9-94db-19ca1d113ec4
-- title:
--   Qm Cap Comm W: rep sum
-- statement:
--   The Qm Cap Comm W construction uses the rep sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/Transfer.lean#L123-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/Transfer.lean#L123-L130

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Transfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open QmCapCommW
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem QmCapCommW.rep_sum {ι : Type*} [Fintype ι] (c : ι → ℂ) {F : ι → Mx k r → E} {x : ι → SS k r i D E}
    (h : ∀ j, Rep (F j) (x j).1) : Rep (fun g => ∑ j, c j • F j g) (∑ j, c j • x j).1 := by sorry
