-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_H_of_mem
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.QRG.H_of_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:07.143676+00:00
-- url     : https://prove2.me/theorems/3092923e-ea87-4e48-a9fe-d1c5d06913f7
-- title:
--   QRG: H of mem
-- statement:
--   The QRG construction uses the H of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertGen.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertGen.lean#L99-L102

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.QRG.H_of_mem (g : GL (Fin n) K) (hg : g ∈ UJ σ J) (x y : Fin n → K) :
    H σ J ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) ((g : Matrix (Fin n) (Fin n) K) *ᵥ y) = H σ J x y := by sorry
