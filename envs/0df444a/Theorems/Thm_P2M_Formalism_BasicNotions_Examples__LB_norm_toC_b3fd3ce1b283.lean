-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_norm_toC_b3fd3ce1b283
-- name    : P2M_Formalism_BasicNotions_Examples__LB_norm_toC_b3fd3ce1b283
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:32:47.52803+00:00
-- url     : https://prove2.me/theorems/d9a751fd-cb03-543e-8e7e-50afea3ce062
-- title:
--   P2 M Formalism Basic Notions Examples  LB norm to C b3fd3ce1b283: P2 M Formalism Basic Notions Examples  LB norm to C b3fd3ce1b283
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB norm to C b3fd3ce1b283 construction uses the P2 M Formalism Basic Notions Examples  LB norm to C b3fd3ce1b283 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L82-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L82-L82

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

theorem P2M_Formalism_BasicNotions_Examples__LB_norm_toC_b3fd3ce1b283 (a : ↥(OL LL)) : ‖toC LL a‖ = nrm LL a := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«norm_toC» := P2M_Formalism_BasicNotions_Examples__LB_norm_toC_b3fd3ce1b283
