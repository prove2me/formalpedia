-- Prove2me | Theorems.Thm_PI_Dv_ProjCW_locLe_map
-- name    : PI.Dv.ProjCW.locLe_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:04.605231+00:00
-- url     : https://prove2.me/theorems/a5f2b325-c631-4322-8bed-4978fce0d83e
-- title:
--   Proj CW: loc Le map
-- statement:
--   The Proj CW construction uses the loc Le map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSpans/SpanPowSmul.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSpans/SpanPowSmul.lean#L16-L23

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

theorem PI.Dv.ProjCW.locLe_map (w : HeightOneSpectrum (𝓞 K)) (F : ℕ) (M N : Submodule (𝓞 K) V)
    (f : V →ₗ[𝓞 K] V) (h : LocLe w F M N) : LocLe w F (M.map f) (N.map f) := by sorry
