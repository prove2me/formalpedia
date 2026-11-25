-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_stdH_good_97378cacea4e
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_stdH_good_97378cacea4e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:49:01.419768+00:00
-- url     : https://prove2.me/theorems/375a0f33-921a-4ac4-ab3e-263de8a348f3
-- title:
--   P2 M Formalism Basic Notions Examples  NZ std H good 97378cacea4e: P2 M Formalism Basic Notions Examples  NZ std H good 97378cacea4e
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ std H good 97378cacea4e construction uses the P2 M Formalism Basic Notions Examples  NZ std H good 97378cacea4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L64-L65

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA
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
open NumberField IsDedekindDomain Formalism.BasicNotions
variable (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)

theorem P2M_Formalism_BasicNotions_Examples__NZ_stdH_good_97378cacea4e : (stdH K n).Good := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«stdH_good» := P2M_Formalism_BasicNotions_Examples__NZ_stdH_good_97378cacea4e
