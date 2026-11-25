-- Prove2me | Theorems.Thm_PI_MkQ_phi_injective
-- name    : PI.MkQ.phi_injective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:35:46.951418+00:00
-- url     : https://prove2.me/theorems/81c1dbdd-1e6a-4751-a5f8-3b22336efea3
-- title:
--   Mk Q: phi injective
-- statement:
--   The Mk Q construction uses the phi injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiTorsionFree/Lattice.lean#L103-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiTorsionFree/Lattice.lean#L103-L120

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
variable [Finite G]

theorem PI.MkQ.phi_injective : Function.Injective (phi G) := by sorry
