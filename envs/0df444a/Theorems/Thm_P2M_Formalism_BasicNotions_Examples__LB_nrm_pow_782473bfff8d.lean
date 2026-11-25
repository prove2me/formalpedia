-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_nrm_pow_782473bfff8d
-- name    : P2M_Formalism_BasicNotions_Examples__LB_nrm_pow_782473bfff8d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:34:15.749265+00:00
-- url     : https://prove2.me/theorems/8b3258f7-2642-4aaf-9102-3c99f4bce6c1
-- title:
--   P2 M Formalism Basic Notions Examples  LB nrm pow 782473bfff8d: P2 M Formalism Basic Notions Examples  LB nrm pow 782473bfff8d
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB nrm pow 782473bfff8d construction uses the P2 M Formalism Basic Notions Examples  LB nrm pow 782473bfff8d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L53-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L53-L53

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

theorem P2M_Formalism_BasicNotions_Examples__LB_nrm_pow_782473bfff8d (a : ↥(OL LL)) (n : ℕ) : nrm LL (a ^ n) = nrm LL a ^ n := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«nrm_pow» := P2M_Formalism_BasicNotions_Examples__LB_nrm_pow_782473bfff8d
