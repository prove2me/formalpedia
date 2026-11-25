-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_OL_adic_6178b45ff505
-- name    : P2M_Formalism_BasicNotions_Examples__LB_OL_adic_6178b45ff505
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T16:34:36.011801+00:00
-- url     : https://prove2.me/theorems/676ac448-d50c-49ce-87cc-25e843bbf2a7
-- title:
--   P2 M Formalism Basic Notions Examples  LB OL adic 6178b45ff505: P2 M Formalism Basic Notions Examples  LB OL adic 6178b45ff505
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB OL adic 6178b45ff505 construction uses the P2 M Formalism Basic Notions Examples  LB OL adic 6178b45ff505 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L55-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L55-L75

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

theorem P2M_Formalism_BasicNotions_Examples__LB_OL_adic_6178b45ff505 : IsAdic (maximalIdeal ↥(OL LL)) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«OL_adic» := P2M_Formalism_BasicNotions_Examples__LB_OL_adic_6178b45ff505
