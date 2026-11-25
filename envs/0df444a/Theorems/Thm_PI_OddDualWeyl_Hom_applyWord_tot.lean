-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Hom_applyWord_tot
-- name    : PI.OddDualWeyl.Hom.applyWord_tot
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:34:56.009274+00:00
-- url     : https://prove2.me/theorems/0713723e-2af9-56a6-94c1-5f322dcbc7ea
-- title:
--   Hom: apply Word tot
-- statement:
--   The Hom construction uses the apply Word tot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L184-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L184-L188

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open PI.OddDualWeyl.Hom
variable {R : Type} [CommRing R] {k : ℕ}
variable {wt : Fin k × Fin k → ℤ} {δ : ℤ}

theorem PI.OddDualWeyl.Hom.applyWord_tot (wd : List (Fin k × Fin k × ℕ)) {f : MvPolynomial (Fin k × Fin k) R} {n : ℕ}
    (hf : IsHomogeneous f n) : IsHomogeneous (applyWord R wd f) n := by sorry
