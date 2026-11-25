-- Prove2me | Theorems.Thm_PI_Dv_ProjBW_mem_range_iff
-- name    : PI.Dv.ProjBW.mem_range_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:27.435874+00:00
-- url     : https://prove2.me/theorems/de84bdbe-fb99-599c-9d4f-dd322591d0dc
-- title:
--   Proj BW: mem range iff
-- statement:
--   The Proj BW construction uses the mem range iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MajorantVanishing/MajAtZeroRight.lean#L52-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MajorantVanishing/MajAtZeroRight.lean#L52-L58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MajorantVanishing_MajAtZeroRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjBW
open NumberField Formalism.HN
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem PI.Dv.ProjBW.mem_range_iff {V : Type} [AddCommGroup V] [Module K V] (e : Module.End K V) (he : e * e = e) (x : V) :
    x ∈ LinearMap.range e ↔ e x = x := by sorry
