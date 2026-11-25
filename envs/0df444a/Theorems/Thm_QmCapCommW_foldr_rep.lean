-- Prove2me | Theorems.Thm_QmCapCommW_foldr_rep
-- name    : QmCapCommW.foldr_rep
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:05:55.667678+00:00
-- url     : https://prove2.me/theorems/922d8afe-e360-4de8-9e77-cb88df89c12f
-- title:
--   Qm Cap Comm W: foldr rep
-- statement:
--   The Qm Cap Comm W construction uses the foldr rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/Transfer.lean#L153-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/Transfer.lean#L153-L164

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

theorem QmCapCommW.foldr_rep (hC : CapCongr) (hP : EabPres) (hD : IsOpen D) (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i)))
    {F : Mx k r → E} {x : SS k r i D E} (h : Rep F x.1) :
    Rep ((l.map fun p => Formalism.QuantumDeterminants.Top (EH k r) p.1 (posL k r i p.2.1) (posL k r i p.2.2)).foldr (fun T f => T f) F)
      ((l.map fun p => Tm (EE hP hD) p.1 p.2.1 p.2.2).prod x).1 := by sorry
