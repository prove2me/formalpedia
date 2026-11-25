-- Prove2me | Theorems.Thm_QmCapCommW_Tm_rep
-- name    : QmCapCommW.Tm_rep
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:51:34.503362+00:00
-- url     : https://prove2.me/theorems/28770852-16e4-483a-9165-3af2e458c702
-- title:
--   Qm Cap Comm W: Tm rep
-- statement:
--   The Qm Cap Comm W construction uses the Tm rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/Transfer.lean#L137-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/Transfer.lean#L137-L151

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

theorem QmCapCommW.Tm_rep (hC : CapCongr) (hP : EabPres) (hD : IsOpen D) {F : Mx k r → E} {x : SS k r i D E}
    (h : Rep F x.1) (u : ℂ) (a b : Fin (mdim k r i)) :
    Rep (Formalism.QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) F) (Tm (EE hP hD) u a b x).1 := by sorry
