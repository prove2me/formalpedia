-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Hom_weight_cast
-- name    : PI.OddDualWeyl.Hom.weight_cast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:52.274587+00:00
-- url     : https://prove2.me/theorems/99f9cfb0-6886-48d5-a8fa-4c3a7c26579c
-- title:
--   Hom: weight cast
-- statement:
--   The Hom construction uses the weight cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L125-L127

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

theorem PI.OddDualWeyl.Hom.weight_cast (w : Fin k × Fin k → ℕ) (α : Fin k × Fin k →₀ ℕ) :
    Finsupp.weight (fun v => (w v : ℤ)) α = (Finsupp.weight w α : ℤ) := by sorry
