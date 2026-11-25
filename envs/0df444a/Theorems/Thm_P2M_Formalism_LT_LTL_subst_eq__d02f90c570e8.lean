-- Prove2me | Theorems.Thm_P2M_Formalism_LT_LTL_subst_eq__d02f90c570e8
-- name    : P2M_Formalism_LT_LTL_subst_eq__d02f90c570e8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:04.422501+00:00
-- url     : https://prove2.me/theorems/07d1eb20-61d9-4355-b8d1-59ad2a5bd1fa
-- title:
--   P2 M Formalism LT LTL subst eq  d02f90c570e8: P2 M Formalism LT LTL subst eq  d02f90c570e8
-- statement:
--   The P2 M Formalism LT LTL subst eq  d02f90c570e8 construction uses the P2 M Formalism LT LTL subst eq  d02f90c570e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L93-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L93-L99

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

theorem P2M_Formalism_LT_LTL_subst_eq__d02f90c570e8 (f : PowerSeries K) (h0 : constantCoeff f = 0) {a : MvPowerSeries ι K}
    (ha0 : MvPowerSeries.constantCoeff a = 0) :
    f.subst a = coeff 1 f • a + a ^ 2 * (tail2 f).subst a := by sorry

alias «Formalism».«LT».«LTL».«subst_eq'» := P2M_Formalism_LT_LTL_subst_eq__d02f90c570e8
