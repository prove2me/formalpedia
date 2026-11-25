-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_evF_infIdele
-- name    : PI.AlgValsFin.W.evF_infIdele
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:22:33.758107+00:00
-- url     : https://prove2.me/theorems/b4c20170-2821-441e-a70b-3e6a768896ba
-- title:
--   W: ev F inf Idele
-- statement:
--   The W construction uses the ev F inf Idele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/EvFLocalIdeleSelf.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/EvFLocalIdeleSelf.lean#L32-L34

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

theorem PI.AlgValsFin.W.evF_infIdele (v : HeightOneSpectrum (𝓞 L)) (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    evF v (infIdele L w x) = 1 := by sorry
