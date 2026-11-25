-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_F_hasCMByIsogeny_of__5413287b0bf6
-- name    : P2M_Formalism_L2_Th1_F_hasCMByIsogeny_of__5413287b0bf6
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:58:40.672697+00:00
-- url     : https://prove2.me/theorems/1e0e9615-ed4c-4ca6-9709-2b42a01bcfc9
-- title:
--   P2 M Formalism L2 Th1 F has CMBy Isogeny of  5413287b0bf6: P2 M Formalism L2 Th1 F has CMBy Isogeny of  5413287b0bf6
-- statement:
--   The P2 M Formalism L2 Th1 F has CMBy Isogeny of  5413287b0bf6 construction uses the P2 M Formalism L2 Th1 F has CMBy Isogeny of  5413287b0bf6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HasCMByIsogenyOf.lean#L103-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HasCMByIsogenyOf.lean#L103-L104

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HasCMByIsogenyOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM (omegaK HasCMBy)
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F

theorem P2M_Formalism_L2_Th1_F_hasCMByIsogeny_of__5413287b0bf6 (hf : IsogenyFormulaInstance) : HasCMByIsogeny := by sorry

alias «Formalism».«L2».«Th1».«F».«hasCMByIsogeny_of'» := P2M_Formalism_L2_Th1_F_hasCMByIsogeny_of__5413287b0bf6
