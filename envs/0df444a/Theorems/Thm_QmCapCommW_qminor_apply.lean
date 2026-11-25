-- Prove2me | Theorems.Thm_QmCapCommW_qminor_apply
-- name    : QmCapCommW.qminor_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:06:35.977799+00:00
-- url     : https://prove2.me/theorems/66edeac6-e7ce-4e5b-8f19-00b5b283d85a
-- title:
--   Qm Cap Comm W: qminor apply
-- statement:
--   The Qm Cap Comm W construction uses the qminor apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/Transfer.lean#L166-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/Transfer.lean#L166-L175

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

theorem QmCapCommW.qminor_apply (hP : EabPres) (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ)
    (x : SS k r i D E) :
    qminor (EE hP hD) a b u x = ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ)) •
      ((List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)).map
        fun p => Tm (EE hP hD) p.1 p.2.1 p.2.2).prod x := by sorry
