-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_comp_neg__f00b25033542
-- name    : P2M_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_comp_neg__f00b25033542
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:58:34.550602+00:00
-- url     : https://prove2.me/theorems/cc184269-d17a-4a49-a897-3afaf9e12c88
-- title:
--   P2 M PI Unitary Group Mass Formula Ad Index Eq QRG comp neg  f00b25033542: P2 M PI Unitary Group Mass Formula Ad Index Eq QRG comp neg  f00b25033542
-- statement:
--   The P2 M PI Unitary Group Mass Formula Ad Index Eq QRG comp neg  f00b25033542 construction uses the P2 M PI Unitary Group Mass Formula Ad Index Eq QRG comp neg  f00b25033542 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertGen.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertGen.lean#L38-L40

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.QRG
open Matrix Formalism.UG
variable {K : Type} [Field K] {n : ℕ}
variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)

theorem P2M_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_comp_neg__f00b25033542 (x : Fin n → K) : σ ∘ (-x) = -(σ ∘ x) := by sorry

alias «PI».«UnitaryGroupMassFormula».«AdIndexEq».«QRG».«comp_neg'» := P2M_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_comp_neg__f00b25033542
