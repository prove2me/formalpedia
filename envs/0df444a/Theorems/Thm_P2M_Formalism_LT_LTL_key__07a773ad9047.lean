-- Prove2me | Theorems.Thm_P2M_Formalism_LT_LTL_key__07a773ad9047
-- name    : P2M_Formalism_LT_LTL_key__07a773ad9047
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:38:16.975522+00:00
-- url     : https://prove2.me/theorems/e3ca629c-260b-4514-af79-0dd4007a4822
-- title:
--   P2 M Formalism LT LTL key  07a773ad9047: P2 M Formalism LT LTL key  07a773ad9047
-- statement:
--   The P2 M Formalism LT LTL key  07a773ad9047 construction uses the P2 M Formalism LT LTL key  07a773ad9047 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L101-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L101-L116

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] {ι : Type*}

theorem P2M_Formalism_LT_LTL_key__07a773ad9047 [Finite ι] (f : PowerSeries K) (h0 : constantCoeff f = 0)
    {N : ℕ} {a b : MvPowerSeries ι K}
    (ha0 : MvPowerSeries.constantCoeff a = 0) (hb0 : MvPowerSeries.constantCoeff b = 0)
    (hab : Agree N a b) : Low (N + 1) (f.subst a - f.subst b - coeff 1 f • (a - b)) := by sorry

alias «Formalism».«LT».«LTL».«key'» := P2M_Formalism_LT_LTL_key__07a773ad9047
