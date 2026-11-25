-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_evS_zero_1e060cc4a4ba
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_evS_zero_1e060cc4a4ba
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:53:04.300926+00:00
-- url     : https://prove2.me/theorems/88b98e90-ad77-553c-a994-be9c35ae438f
-- title:
--   P2 M Formalism Basic Notions Examples  NZ ev S zero 1e060cc4a4ba: P2 M Formalism Basic Notions Examples  NZ ev S zero 1e060cc4a4ba
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ ev S zero 1e060cc4a4ba construction uses the P2 M Formalism Basic Notions Examples  NZ ev S zero 1e060cc4a4ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L24-L25

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_evS_zero_1e060cc4a4ba {Γ : Type} [Finite Γ] (ψ : Γ → K) : evS ψ (0 : MonoidAlgebra K Γ) = 0 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«evS_zero» := P2M_Formalism_BasicNotions_Examples__NZ_evS_zero_1e060cc4a4ba
