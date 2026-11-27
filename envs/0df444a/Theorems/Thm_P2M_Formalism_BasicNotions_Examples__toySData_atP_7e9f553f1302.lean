-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__toySData_atP_7e9f553f1302
-- name    : P2M_Formalism_BasicNotions_Examples__toySData_atP_7e9f553f1302
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:11:44.044034+00:00
-- url     : https://prove2.me/theorems/dcbe785c-f00e-5152-9626-b6376b6b88ab
-- title:
--   P2 M Formalism Basic Notions Examples  toy SData at P 7e9f553f1302: P2 M Formalism Basic Notions Examples  toy SData at P 7e9f553f1302
-- statement:
--   The P2 M Formalism Basic Notions Examples  toy SData at P 7e9f553f1302 construction uses the P2 M Formalism Basic Notions Examples  toy SData at P 7e9f553f1302 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GPlacesExampleNatAct.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GPlacesExampleNatAct.lean#L84-L85

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

theorem P2M_Formalism_BasicNotions_Examples__toySData_atP_7e9f553f1302 (Del : ℚ) (hDel hgap hlet) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) (p) :
    (toySData sig hc Del hDel hgap hlet loc).atP p = loc p := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«toySData_atP» := P2M_Formalism_BasicNotions_Examples__toySData_atP_7e9f553f1302
