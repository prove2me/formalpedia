-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_stdH_frames_91564ebb4ca5
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_stdH_frames_91564ebb4ca5
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:47:05.045141+00:00
-- url     : https://prove2.me/theorems/3b2975f4-5ce1-4032-8f9a-a13ed5b11119
-- title:
--   P2 M Formalism Basic Notions Examples  NZ std H frames 91564ebb4ca5: P2 M Formalism Basic Notions Examples  NZ std H frames 91564ebb4ca5
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ std H frames 91564ebb4ca5 construction uses the P2 M Formalism Basic Notions Examples  NZ std H frames 91564ebb4ca5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L60-L62

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_stdH_frames_91564ebb4ca5 (v : InfinitePlace K) : IsUnit ((stdH K n).X v).det := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«stdH_frames» := P2M_Formalism_BasicNotions_Examples__NZ_stdH_frames_91564ebb4ca5
