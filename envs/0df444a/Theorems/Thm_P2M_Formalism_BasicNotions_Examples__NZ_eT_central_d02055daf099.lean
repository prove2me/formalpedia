-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_eT_central_d02055daf099
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_eT_central_d02055daf099
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:13.67511+00:00
-- url     : https://prove2.me/theorems/25ba2c15-e2f1-418e-96de-5c2017e928a4
-- title:
--   P2 M Formalism Basic Notions Examples  NZ e T central d02055daf099: P2 M Formalism Basic Notions Examples  NZ e T central d02055daf099
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ e T central d02055daf099 construction uses the P2 M Formalism Basic Notions Examples  NZ e T central d02055daf099 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L100-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L100-L104

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open MonoidAlgebra
attribute [local instance] Classical.propDecidable
variable (K : Type) [Field K] (Γ : Type) [Group Γ] [Finite Γ]
variable {K Γ}

theorem P2M_Formalism_BasicNotions_Examples__NZ_eT_central_d02055daf099 (a : MonoidAlgebra K Γ) : eT K Γ * a = a * eT K Γ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«eT_central» := P2M_Formalism_BasicNotions_Examples__NZ_eT_central_d02055daf099
