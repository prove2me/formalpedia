-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_evI_infIdele_ne
-- name    : PI.AlgValsFin.W.evI_infIdele_ne
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:22:45.58494+00:00
-- url     : https://prove2.me/theorems/4fd31cfd-7c87-5908-a709-afdf5a0023c1
-- title:
--   W: ev I inf Idele ne
-- statement:
--   The W construction uses the ev I inf Idele ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/EvFLocalIdeleSelf.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/EvFLocalIdeleSelf.lean#L49-L51

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

theorem PI.AlgValsFin.W.evI_infIdele_ne (w w' : InfinitePlace L) (h : w' ≠ w) (x : (w.Completion)ˣ) :
    evI w' (infIdele L w x) = 1 := by sorry
