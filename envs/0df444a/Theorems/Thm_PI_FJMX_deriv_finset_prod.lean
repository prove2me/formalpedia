-- Prove2me | Theorems.Thm_PI_FJMX_deriv_finset_prod
-- name    : PI.FJMX.deriv_finset_prod
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:25.605102+00:00
-- url     : https://prove2.me/theorems/ecb83f92-6288-4b71-9f69-4f2711d702db
-- title:
--   FJMX: deriv finset prod
-- statement:
--   The FJMX construction uses the deriv finset prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean#L27-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean#L27-L40

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
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem PI.FJMX.deriv_finset_prod {ι : Type*} [DecidableEq ι] (D : Derivation R A A) (s : Finset ι)
    (f : ι → A) : D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by sorry
