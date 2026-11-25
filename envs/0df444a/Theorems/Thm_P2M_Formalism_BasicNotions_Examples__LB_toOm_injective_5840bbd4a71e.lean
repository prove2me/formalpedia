-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_toOm_injective_5840bbd4a71e
-- name    : P2M_Formalism_BasicNotions_Examples__LB_toOm_injective_5840bbd4a71e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:32:41.401939+00:00
-- url     : https://prove2.me/theorems/07a7d91a-da03-52aa-9c3a-ae5829cc2437
-- title:
--   P2 M Formalism Basic Notions Examples  LB to Om injective 5840bbd4a71e: P2 M Formalism Basic Notions Examples  LB to Om injective 5840bbd4a71e
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB to Om injective 5840bbd4a71e construction uses the P2 M Formalism Basic Notions Examples  LB to Om injective 5840bbd4a71e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L43-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L43-L43

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

theorem P2M_Formalism_BasicNotions_Examples__LB_toOm_injective_5840bbd4a71e : Function.Injective (toOm LL) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«toOm_injective» := P2M_Formalism_BasicNotions_Examples__LB_toOm_injective_5840bbd4a71e
