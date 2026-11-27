-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_toFrac_eq_iff_84d60766bad1
-- name    : P2M_Formalism_BasicNotions_Examples__LB_toFrac_eq_iff_84d60766bad1
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:32:43.629654+00:00
-- url     : https://prove2.me/theorems/1623ab84-b7e0-5bed-97d8-0e30d61a5c8b
-- title:
--   P2 M Formalism Basic Notions Examples  LB to Frac eq iff 84d60766bad1: P2 M Formalism Basic Notions Examples  LB to Frac eq iff 84d60766bad1
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB to Frac eq iff 84d60766bad1 construction uses the P2 M Formalism Basic Notions Examples  LB to Frac eq iff 84d60766bad1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L91-L94

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

theorem P2M_Formalism_BasicNotions_Examples__LB_toFrac_eq_iff_84d60766bad1 (x : ↥LL.1) (a : ↥(OL LL)) :
    algebraMap ↥(OL LL) (FractionRing ↥(OL LL)) a = toFrac LL x ↔ (a : ↥LL.1) = x := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«toFrac_eq_iff» := P2M_Formalism_BasicNotions_Examples__LB_toFrac_eq_iff_84d60766bad1
