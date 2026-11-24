-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Hom_det_isWH
-- name    : PI.OddDualWeyl.Hom.det_isWH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:46.447374+00:00
-- url     : https://prove2.me/theorems/ae2df62e-5367-4d21-92ee-d0056e1dd8ba
-- title:
--   Hom: det is WH
-- statement:
--   The Hom construction uses the det is WH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L141-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L141-L155

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

theorem PI.OddDualWeyl.Hom.det_isWH {M' : Type*} [AddCommMonoid M'] {w : Fin k × Fin k → M'} {s : ℕ}
    (N : Matrix (Fin s) (Fin s) (MvPolynomial (Fin k × Fin k) R)) (r : Fin s → M')
    (h : ∀ p q, IsWeightedHomogeneous w (N p q) (r p)) :
    IsWeightedHomogeneous w N.det (∑ p, r p) := by sorry
