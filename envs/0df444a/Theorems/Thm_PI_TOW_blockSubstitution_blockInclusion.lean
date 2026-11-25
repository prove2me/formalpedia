-- Prove2me | Theorems.Thm_PI_TOW_blockSubstitution_blockInclusion
-- name    : PI.TOW.blockSubstitution_blockInclusion
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:37:25.251932+00:00
-- url     : https://prove2.me/theorems/79623ab9-4f8e-4e32-8a13-9f27f7ad0798
-- title:
--   TOW: block Substitution block Inclusion
-- statement:
--   The TOW construction uses the block Substitution block Inclusion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FockLin.lean#L145-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FockLin.lean#L145-L152

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin
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
open PI PI.TOW
open PI.TO

theorem PI.TOW.blockSubstitution_blockInclusion {K : Type} [CommRing K] {n' m : ℕ} (vec : Fin n' → Bool) (t : Fin n')
    (P : MvPolynomial (Fin (m + 1)) K) :
    Th0 K m vec (embS K t P) = blockEmb K t (theta K m (vec t) P) := by sorry
