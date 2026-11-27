-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_OL_resFinite_1895d1dcc471
-- name    : P2M_Formalism_BasicNotions_Examples__LB_OL_resFinite_1895d1dcc471
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:32:47.577715+00:00
-- url     : https://prove2.me/theorems/6f95929c-aa79-523a-972e-b819479ab425
-- title:
--   P2 M Formalism Basic Notions Examples  LB OL res Finite 1895d1dcc471: P2 M Formalism Basic Notions Examples  LB OL res Finite 1895d1dcc471
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB OL res Finite 1895d1dcc471 construction uses the P2 M Formalism Basic Notions Examples  LB OL res Finite 1895d1dcc471 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L25-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean#L25-L37

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

theorem P2M_Formalism_BasicNotions_Examples__LB_OL_resFinite_1895d1dcc471 : Finite (ResidueField ↥(OL LL)) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«OL_resFinite» := P2M_Formalism_BasicNotions_Examples__LB_OL_resFinite_1895d1dcc471
