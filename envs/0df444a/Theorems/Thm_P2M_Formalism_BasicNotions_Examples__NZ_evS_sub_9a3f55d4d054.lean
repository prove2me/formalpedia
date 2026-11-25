-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_evS_sub_9a3f55d4d054
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_evS_sub_9a3f55d4d054
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:56:36.547915+00:00
-- url     : https://prove2.me/theorems/d60a8455-612b-520c-83cb-782eb5104c9c
-- title:
--   P2 M Formalism Basic Notions Examples  NZ ev S sub 9a3f55d4d054: P2 M Formalism Basic Notions Examples  NZ ev S sub 9a3f55d4d054
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ ev S sub 9a3f55d4d054 construction uses the P2 M Formalism Basic Notions Examples  NZ ev S sub 9a3f55d4d054 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L27-L28

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
variable {K : Type} [Field K]

theorem P2M_Formalism_BasicNotions_Examples__NZ_evS_sub_9a3f55d4d054 {Γ : Type} [Finite Γ] (ψ : Γ → K) (x y : MonoidAlgebra K Γ) : evS ψ (x - y) = evS ψ x - evS ψ y := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«evS_sub» := P2M_Formalism_BasicNotions_Examples__NZ_evS_sub_9a3f55d4d054
