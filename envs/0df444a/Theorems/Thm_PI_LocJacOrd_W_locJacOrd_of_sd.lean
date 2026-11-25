-- Prove2me | Theorems.Thm_PI_LocJacOrd_W_locJacOrd_of_sd
-- name    : PI.LocJacOrd.W.locJacOrd_of_sd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:16:46.205108+00:00
-- url     : https://prove2.me/theorems/e2463016-bd9f-4f10-abe1-d239be760b22
-- title:
--   W: loc Jac Ord of sd
-- statement:
--   The W construction uses the loc Jac Ord of sd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianOrder/LocJacOrdOfSd.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianOrder/LocJacOrdOfSd.lean#L10-L14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_SecondCountableFv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_LocJacOrdOfSd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocJacOrd PI.LocJacOrd.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacOrd

theorem PI.LocJacOrd.W.locJacOrd_of_sd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (h0 : SdNormO (E := E) ψ v)
    (hB : BoxScale) : LocJacOrd (E := E) ψ v := by sorry
