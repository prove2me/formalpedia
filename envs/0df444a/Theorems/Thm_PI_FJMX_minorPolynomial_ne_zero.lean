-- Prove2me | Theorems.Thm_PI_FJMX_minorPolynomial_ne_zero
-- name    : PI.FJMX.minorPolynomial_ne_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:45:09.421531+00:00
-- url     : https://prove2.me/theorems/9ddd2ee3-506f-48f6-8acd-741e0f00e8ef
-- title:
--   FJMX: minor Polynomial ne zero
-- statement:
--   The FJMX construction uses the minor Polynomial ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean#L95-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean#L95-L106

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

theorem PI.FJMX.minorPolynomial_ne_zero [IsDomain R] {k : ℕ} (g : Fin k → Fin k → σ)
    (hg : Function.Injective (fun x : Fin k × Fin k => g x.1 x.2)) : minorPolynomial R g ≠ 0 := by sorry
