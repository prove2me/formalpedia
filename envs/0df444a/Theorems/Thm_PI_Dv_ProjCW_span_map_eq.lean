-- Prove2me | Theorems.Thm_PI_Dv_ProjCW_span_map_eq
-- name    : PI.Dv.ProjCW.span_map_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:14.528713+00:00
-- url     : https://prove2.me/theorems/2378a0c3-ce5b-52f0-a981-9753edb06c8c
-- title:
--   Proj CW: span map eq
-- statement:
--   The Proj CW construction uses the span map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSpans/SpanPowSmul.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSpans/SpanPowSmul.lean#L25-L28

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

theorem PI.Dv.ProjCW.span_map_eq (φ : V →ₗ[K] V) (M : Submodule (𝓞 K) V) (hM : Submodule.span K (M : Set V) = ⊤) :
    Submodule.span K ((M.map (φ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) =
      LinearMap.range φ := by sorry
