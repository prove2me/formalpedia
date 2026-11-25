-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_toC_injective_798127f4eebf
-- name    : P2M_Formalism_BasicNotions_Examples__LB_toC_injective_798127f4eebf
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T16:33:20.304078+00:00
-- url     : https://prove2.me/theorems/c3844089-473e-449d-b3fe-9dc81aacceb1
-- title:
--   P2 M Formalism Basic Notions Examples  LB to C injective 798127f4eebf: P2 M Formalism Basic Notions Examples  LB to C injective 798127f4eebf
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB to C injective 798127f4eebf construction uses the P2 M Formalism Basic Notions Examples  LB to C injective 798127f4eebf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L79-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L79-L80

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

theorem P2M_Formalism_BasicNotions_Examples__LB_toC_injective_798127f4eebf : Function.Injective (toC LL) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«toC_injective» := P2M_Formalism_BasicNotions_Examples__LB_toC_injective_798127f4eebf
