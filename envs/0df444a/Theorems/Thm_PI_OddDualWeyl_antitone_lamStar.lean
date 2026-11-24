-- Prove2me | Theorems.Thm_PI_OddDualWeyl_antitone_lamStar
-- name    : PI.OddDualWeyl.antitone_lamStar
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:04.493487+00:00
-- url     : https://prove2.me/theorems/afb71df6-9947-4cd4-b5a5-1d255dacb421
-- title:
--   Odd Dual Weyl: antitone lam Star
-- statement:
--   The Odd Dual Weyl construction uses the antitone lam Star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L138-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/RevColOneTranspose.lean#L138-L141

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose
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
variable {K : Type} [Field K]

theorem PI.OddDualWeyl.antitone_lamStar {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone (lamStar lam) := by sorry
