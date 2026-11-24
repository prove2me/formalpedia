-- Prove2me | Theorems.Thm_PI_FJMX_minorPolynomial_isWeightedHomogeneous
-- name    : PI.FJMX.minorPolynomial_isWeightedHomogeneous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:57.956714+00:00
-- url     : https://prove2.me/theorems/2a82d7b5-fc58-4e56-9d45-bc51805d59cb
-- title:
--   FJMX: minor Polynomial is Weighted Homogeneous
-- statement:
--   The FJMX construction uses the minor Polynomial is Weighted Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean#L108-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean#L108-L129

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.FJMX
variable {R : Type*} [CommRing R] {σ : Type*}

theorem PI.FJMX.minorPolynomial_isWeightedHomogeneous {k : ℕ} (g : Fin k → Fin k → σ) (w : σ → ℕ) (u v : Fin k → ℕ)
    (hw : ∀ i j, w (g i j) = u i + v j) :
    IsWeightedHomogeneous w (minorPolynomial R g) (∑ i, u i + ∑ j, v j) := by sorry
