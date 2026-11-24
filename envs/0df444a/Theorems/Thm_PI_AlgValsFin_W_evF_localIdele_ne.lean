-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_evF_localIdele_ne
-- name    : PI.AlgValsFin.W.evF_localIdele_ne
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:03:56.777436+00:00
-- url     : https://prove2.me/theorems/1d2f323a-abbe-4605-a6c4-4e2a4eccc10f
-- title:
--   W: ev F local Idele ne
-- statement:
--   The W construction uses the ev F local Idele ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/EvFLocalIdeleSelf.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/EvFLocalIdeleSelf.lean#L40-L43

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

theorem PI.AlgValsFin.W.evF_localIdele_ne (w v : HeightOneSpectrum (𝓞 L)) (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    evF w (localIdele L v x) = 1 := by sorry
