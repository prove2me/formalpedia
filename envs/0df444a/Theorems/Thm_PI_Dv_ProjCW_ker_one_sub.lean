-- Prove2me | Theorems.Thm_PI_Dv_ProjCW_ker_one_sub
-- name    : PI.Dv.ProjCW.ker_one_sub
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:02.951305+00:00
-- url     : https://prove2.me/theorems/04218ec7-8d4c-44d8-b29c-6b1ed826ae7d
-- title:
--   Proj CW: ker one sub
-- statement:
--   The Proj CW construction uses the ker one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSpans/SpanPowSmul.lean#L48-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSpans/SpanPowSmul.lean#L48-L56

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSpans_SpanPowSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjCW
open Formalism.BasicNotions NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.ProjCW.ker_one_sub (e : Module.End K V) (he : e * e = e) :
    LinearMap.ker (1 - e) = LinearMap.range e := by sorry
