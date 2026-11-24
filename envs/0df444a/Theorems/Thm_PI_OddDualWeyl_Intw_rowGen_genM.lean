-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Intw_rowGen_genM
-- name    : PI.OddDualWeyl.Intw.rowGen_genM
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:40.113725+00:00
-- url     : https://prove2.me/theorems/01f6a665-8d91-481e-995d-e4d1bf2b5904
-- title:
--   Intw: row Gen gen M
-- statement:
--   The Intw construction uses the row Gen gen M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/TransvectionMulApply.lean#L63-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/TransvectionMulApply.lean#L63-L69

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

theorem PI.OddDualWeyl.Intw.rowGen_genM (a b : Fin k) :
    (rowGen R a b).toRingHom.mapMatrix (genM R k) =
      transvection b a (Polynomial.X) *
        (Polynomial.C : MvPolynomial (Fin k × Fin k) R →+* _).mapMatrix (genM R k) := by sorry
