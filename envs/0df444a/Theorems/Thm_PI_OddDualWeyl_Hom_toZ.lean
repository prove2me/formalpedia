-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Hom_toZ
-- name    : PI.OddDualWeyl.Hom.toZ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:42.590826+00:00
-- url     : https://prove2.me/theorems/af40ecc7-31b8-452a-a33e-b13b9465d215
-- title:
--   Hom: to Z
-- statement:
--   The Hom construction uses the to Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L129-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L129-L132

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

theorem PI.OddDualWeyl.Hom.toZ {w : Fin k × Fin k → ℕ} {f : MvPolynomial (Fin k × Fin k) R} {d : ℕ}
    (h : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous (fun v => (w v : ℤ)) f (d : ℤ) := by sorry
