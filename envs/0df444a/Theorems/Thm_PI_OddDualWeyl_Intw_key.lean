-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Intw_key
-- name    : PI.OddDualWeyl.Intw.key
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:14:08.989838+00:00
-- url     : https://prove2.me/theorems/1a842c92-b55f-4f2e-80b8-37586796842d
-- title:
--   Intw: key
-- statement:
--   The Intw construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/TransvectionMulApply.lean#L98-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/TransvectionMulApply.lean#L98-L134

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_TransvectionMulApply
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
open PI.OddDualWeyl.Intw
variable {R : Type} [CommRing R] {k : ℕ}

theorem PI.OddDualWeyl.Intw.key (a b : Fin k) (hab : a ≠ b) (f' : MvPolynomial (Fin k × Fin k) R) :
    rowGen R a b (dualSub R k f') =
      (Polynomial.map (dualSub R k : MvPolynomial (Fin k × Fin k) R →+* _)
        (rowGen R b a f')).comp (-Polynomial.X) := by sorry
