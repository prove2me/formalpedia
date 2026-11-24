-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_evF_val
-- name    : PI.AlgValsFin.W.evF_val
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:03:43.478785+00:00
-- url     : https://prove2.me/theorems/6330fcec-4a46-4e6f-8c0e-5160b4c05569
-- title:
--   W: ev F val
-- statement:
--   The W construction uses the ev F val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/EvFLocalIdeleSelf.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/EvFLocalIdeleSelf.lean#L23-L24

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ValuedAtFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]

theorem PI.AlgValsFin.W.evF_val (v : HeightOneSpectrum (𝓞 L)) (x : Ideles L) :
    ((evF v x : (v.adicCompletion L)ˣ) : v.adicCompletion L) = (x : AdeleRing (𝓞 L) L).2 v := by sorry
