-- Prove2me | Theorems.Thm_PI_IdealLatticeWork_im_comb
-- name    : PI.IdealLatticeWork.im_comb
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:30.084889+00:00
-- url     : https://prove2.me/theorems/773a7087-960b-4ebd-9d25-41be503e11cb
-- title:
--   Ideal Lattice Work: im comb
-- statement:
--   The Ideal Lattice Work construction uses the im comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdealLatticeBasis/Assemble.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdealLatticeBasis/Assemble.lean#L15-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdealLattice
import Definitions.Def_Formalism_PeriodIntegrals_AreaLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdealLatticeBasis_IdealBasisAlt
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AreaLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdealLatticeBasis_Assemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.IdealLatticeWork

theorem PI.IdealLatticeWork.im_comb (u v : ℂ) (p q r s : ℤ) :
    ((starRingEnd ℂ) ((p : ℂ) * u + (q : ℂ) * v) * ((r : ℂ) * u + (s : ℂ) * v)).im
      = ((p * s - q * r : ℤ) : ℝ) * ((starRingEnd ℂ) u * v).im := by sorry
