-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_F_Homog_wEta_basis__f3ec1ad0cd44
-- name    : P2M_Formalism_L2_Th1_F_Homog_wEta_basis__f3ec1ad0cd44
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:58:26.106502+00:00
-- url     : https://prove2.me/theorems/0022ab40-ef20-41e1-a733-17e7202aad11
-- title:
--   P2 M Formalism L2 Th1 F Homog w Eta basis  f3ec1ad0cd44: P2 M Formalism L2 Th1 F Homog w Eta basis  f3ec1ad0cd44
-- statement:
--   The P2 M Formalism L2 Th1 F Homog w Eta basis  f3ec1ad0cd44 construction uses the P2 M Formalism L2 Th1 F Homog w Eta basis  f3ec1ad0cd44 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/LatticeOnly.lean#L211-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/LatticeOnly.lean#L211-L218

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Homog
variable (L : PeriodPair) (c : ℂ) (hc : c ≠ 0)

theorem P2M_Formalism_L2_Th1_F_Homog_wEta_basis__f3ec1ad0cd44 (L : PeriodPair) : wEta L L.ω₁ = 2 * wZeta L (L.ω₁ / 2) := by sorry

alias «Formalism».«L2».«Th1».«F».«Homog».«wEta_basis₁» := P2M_Formalism_L2_Th1_F_Homog_wEta_basis__f3ec1ad0cd44
