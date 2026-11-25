-- Prove2me | Theorems.Thm_PI_MkQ_rho_apply_coe
-- name    : PI.MkQ.rho_apply_coe
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:35:02.860865+00:00
-- url     : https://prove2.me/theorems/5264131e-98e5-589a-9fcc-19d88ef9b08e
-- title:
--   Mk Q: rho apply coe
-- statement:
--   The Mk Q construction uses the rho apply coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiTorsionFree/Lattice.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiTorsionFree/Lattice.lean#L57-L59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MinkowskiQ
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_Minkowski
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiTorsionFree_Lattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.MkQ
open Matrix
variable {N : ℕ} (G : Subgroup (GeneralLinearGroup (Fin N) ℚ))

theorem PI.MkQ.rho_apply_coe (g : G) (v : lat G) :
    ((rho G g v : lat G) : Fin N → ℚ) =
      ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec v := by sorry
