-- Prove2me | Theorems.Thm_PI_FJMX_minorPolynomial_mem_supported
-- name    : PI.FJMX.minorPolynomial_mem_supported
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:45:07.680819+00:00
-- url     : https://prove2.me/theorems/cd6b3dee-fd59-4eae-869d-8aa516728f19
-- title:
--   FJMX: minor Polynomial mem supported
-- statement:
--   The FJMX construction uses the minor Polynomial mem supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean#L131-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean#L131-L142

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

theorem PI.FJMX.minorPolynomial_mem_supported {k : ℕ} (g : Fin k → Fin k → σ) (S : Set σ) (hS : ∀ i j, g i j ∈ S) :
    minorPolynomial R g ∈ supported R S := by sorry
