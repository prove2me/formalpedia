-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_wEta____42cf7b73a011
-- name    : P2M_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_wEta____42cf7b73a011
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:58:24.837706+00:00
-- url     : https://prove2.me/theorems/3b2c62be-ccbd-40ce-9842-2d60da369744
-- title:
--   P2 M Formalism L2 Th1 F Weierstrass Zeta Quasi Period w Eta    42cf7b73a011: P2 M Formalism L2 Th1 F Weierstrass Zeta Quasi Period w Eta    42cf7b73a011
-- statement:
--   The P2 M Formalism L2 Th1 F Weierstrass Zeta Quasi Period w Eta    42cf7b73a011 construction uses the P2 M Formalism L2 Th1 F Weierstrass Zeta Quasi Period w Eta    42cf7b73a011 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ZetaQuasi.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ZetaQuasi.lean#L44-L46

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ZetaQuasi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod

theorem P2M_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_wEta____42cf7b73a011 (L : PeriodPair) : wEta L L.ω₁ = 2 * wZeta L (L.ω₁ / 2) := by sorry

alias «Formalism».«L2».«Th1».«F».«WeierstrassZetaQuasiPeriod».«wEta_ω₁» := P2M_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_wEta____42cf7b73a011
