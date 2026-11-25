-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_val_inv_sub
-- name    : PI.AlgValsFin.W.val_inv_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:23:09.261495+00:00
-- url     : https://prove2.me/theorems/daa6f821-99bd-4794-8c1c-c6c58a7402a2
-- title:
--   W: val inv sub
-- statement:
--   The W construction uses the val inv sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/InvMemUFin.lean#L43-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/InvMemUFin.lean#L43-L52

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_InvMemUFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Neutral.B1 Topology
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]

theorem PI.AlgValsFin.W.val_inv_sub {x : Ideles L} (hx : x ∈ UFin L) (v : HeightOneSpectrum (𝓞 L)) :
    Valued.v ((x⁻¹ : Ideles L).val.2 v - 1) = Valued.v ((x : AdeleRing (𝓞 L) L).2 v - 1) := by sorry
