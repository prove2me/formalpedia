-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_wEta____81bf5efe9be8
-- name    : P2M_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_wEta____81bf5efe9be8
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:58:28.049551+00:00
-- url     : https://prove2.me/theorems/9e6d5aef-4454-44b1-a1f9-faacc8a6bc57
-- title:
--   P2 M Formalism L2 Th1 F Weierstrass Zeta Quasi Period w Eta    81bf5efe9be8: P2 M Formalism L2 Th1 F Weierstrass Zeta Quasi Period w Eta    81bf5efe9be8
-- statement:
--   The P2 M Formalism L2 Th1 F Weierstrass Zeta Quasi Period w Eta    81bf5efe9be8 construction uses the P2 M Formalism L2 Th1 F Weierstrass Zeta Quasi Period w Eta    81bf5efe9be8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ZetaQuasi.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ZetaQuasi.lean#L48-L50

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

theorem P2M_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_wEta____81bf5efe9be8 (L : PeriodPair) : wEta L L.ω₂ = 2 * wZeta L (L.ω₂ / 2) := by sorry

alias «Formalism».«L2».«Th1».«F».«WeierstrassZetaQuasiPeriod».«wEta_ω₂» := P2M_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_wEta____81bf5efe9be8
