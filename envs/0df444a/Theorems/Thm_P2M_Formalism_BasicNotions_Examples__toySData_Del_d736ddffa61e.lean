-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__toySData_Del_d736ddffa61e
-- name    : P2M_Formalism_BasicNotions_Examples__toySData_Del_d736ddffa61e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:10:52.70835+00:00
-- url     : https://prove2.me/theorems/1c847ec8-a03d-5fa5-b42c-0b5c69d3ab11
-- title:
--   P2 M Formalism Basic Notions Examples  toy SData Del d736ddffa61e: P2 M Formalism Basic Notions Examples  toy SData Del d736ddffa61e
-- statement:
--   The P2 M Formalism Basic Notions Examples  toy SData Del d736ddffa61e construction uses the P2 M Formalism Basic Notions Examples  toy SData Del d736ddffa61e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GPlacesExampleNatAct.lean#L87-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GPlacesExampleNatAct.lean#L87-L88

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_DataS
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GPlacesExampleNatAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Formalism.BasicNotions NumberField IsDedekindDomain
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (sig : E →ₐ[F] E)
variable {Word Tau : Type} [Subsingleton Word] (hc : Word → Tau → HCParam R)
variable {sig hc}

theorem P2M_Formalism_BasicNotions_Examples__toySData_Del_d736ddffa61e (Del : ℚ) (hDel hgap hlet) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) :
    (toySData sig hc Del hDel hgap hlet loc).Del = Del := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«toySData_Del» := P2M_Formalism_BasicNotions_Examples__toySData_Del_d736ddffa61e
