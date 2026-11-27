-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_norm_aut_906809479f72
-- name    : P2M_Formalism_BasicNotions_Examples__LB_norm_aut_906809479f72
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:09:26.617933+00:00
-- url     : https://prove2.me/theorems/aa17fe37-18a5-574a-b1ef-dec53607f223
-- title:
--   P2 M Formalism Basic Notions Examples  LB norm aut 906809479f72: P2 M Formalism Basic Notions Examples  LB norm aut 906809479f72
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB norm aut 906809479f72 construction uses the P2 M Formalism Basic Notions Examples  LB norm aut 906809479f72 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocB.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocB.lean#L76-L78

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocB
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
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  (j : Ω →+* PadicAlgCl l)

theorem P2M_Formalism_BasicNotions_Examples__LB_norm_aut_906809479f72 (σ : GQ l) (x : PadicAlgCl l) : ‖σ x‖ = ‖x‖ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«norm_aut» := P2M_Formalism_BasicNotions_Examples__LB_norm_aut_906809479f72
