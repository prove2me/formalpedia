-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_toOm_apply_83828b1ee190
-- name    : P2M_Formalism_BasicNotions_Examples__LB_toOm_apply_83828b1ee190
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T16:34:23.508981+00:00
-- url     : https://prove2.me/theorems/e2441450-e756-4af0-a1c7-477d2d381ecd
-- title:
--   P2 M Formalism Basic Notions Examples  LB to Om apply 83828b1ee190: P2 M Formalism Basic Notions Examples  LB to Om apply 83828b1ee190
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB to Om apply 83828b1ee190 construction uses the P2 M Formalism Basic Notions Examples  LB to Om apply 83828b1ee190 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L41-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L41-L41

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

theorem P2M_Formalism_BasicNotions_Examples__LB_toOm_apply_83828b1ee190 (a : ↥(OL LL)) : toOm LL a = ((a : ↥LL.1) : PadicAlgCl l) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«toOm_apply» := P2M_Formalism_BasicNotions_Examples__LB_toOm_apply_83828b1ee190
