-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_toFrac_coe_70b127540ffe
-- name    : P2M_Formalism_BasicNotions_Examples__LB_toFrac_coe_70b127540ffe
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:32:41.626972+00:00
-- url     : https://prove2.me/theorems/435fd8ad-3f6a-5cc2-b76c-3395a46e0e1c
-- title:
--   P2 M Formalism Basic Notions Examples  LB to Frac coe 70b127540ffe: P2 M Formalism Basic Notions Examples  LB to Frac coe 70b127540ffe
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB to Frac coe 70b127540ffe construction uses the P2 M Formalism Basic Notions Examples  LB to Frac coe 70b127540ffe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L86-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L86-L89

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] (LL : FinExt l)

theorem P2M_Formalism_BasicNotions_Examples__LB_toFrac_coe_70b127540ffe (a : ↥(OL LL)) : toFrac LL (a : ↥LL.1) = algebraMap ↥(OL LL) (FractionRing ↥(OL LL)) a := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«toFrac_coe» := P2M_Formalism_BasicNotions_Examples__LB_toFrac_coe_70b127540ffe
