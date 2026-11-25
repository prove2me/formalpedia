-- Prove2me | Theorems.Thm_PI_Dv_ProjCW_span_pow_smul
-- name    : PI.Dv.ProjCW.span_pow_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:19.500589+00:00
-- url     : https://prove2.me/theorems/5e3372aa-38ad-5969-853f-cb7eac274e76
-- title:
--   Proj CW: span pow smul
-- statement:
--   The Proj CW construction uses the span pow smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSpans/SpanPowSmul.lean#L30-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSpans/SpanPowSmul.lean#L30-L46

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

theorem PI.Dv.ProjCW.span_pow_smul (w : HeightOneSpectrum (𝓞 K)) (F : ℕ) (N : Submodule (𝓞 K) V) :
    Submodule.span K ((((w.asIdeal ^ F) • N : Submodule (𝓞 K) V)) : Set V) =
      Submodule.span K (N : Set V) := by sorry
