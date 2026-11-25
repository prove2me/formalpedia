-- Prove2me | Theorems.Thm_PI_AprimeInfW_herm_cross
-- name    : PI.AprimeInfW.herm_cross
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:06.866774+00:00
-- url     : https://prove2.me/theorems/bd948412-f915-47fc-b76d-b747a8a0ffd1
-- title:
--   Aprime Inf W: herm cross
-- statement:
--   The Aprime Inf W construction uses the herm cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/MpOfIsomProd.lean#L82-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/MpOfIsomProd.lean#L82-L93

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_MpOfIsomProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW
open MeasureTheory Matrix ComplexConjugate

theorem PI.AprimeInfW.herm_cross {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (∑ i, ∑ j, A i j * conj (B i j)).im = 0 := by sorry
