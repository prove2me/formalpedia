-- Prove2me | Theorems.Thm_PI_PolynomialProperness_unipotent_fixes_frame_vector
-- name    : PI.PolynomialProperness.unipotent_fixes_frame_vector
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:37:09.159242+00:00
-- url     : https://prove2.me/theorems/680732f6-b39c-5e53-93b7-c86924fe1e15
-- title:
--   Polynomial Properness: unipotent fixes frame vector
-- statement:
--   The Polynomial Properness construction uses the unipotent fixes frame vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/UnipotentFixesFrameVector.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/UnipotentFixesFrameVector.lean#L24-L29

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnipotentFixesFrameVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness

theorem PI.PolynomialProperness.unipotent_fixes_frame_vector (hU : UMapFrame) {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : StdZ k r z)
    {n0 : B.Mat k r} (hn : n0 ∈ N0set k r z) (b : Fin (r + 1)) :
    n0 *ᵥ fvec k r z b = fvec k r z b := by sorry
