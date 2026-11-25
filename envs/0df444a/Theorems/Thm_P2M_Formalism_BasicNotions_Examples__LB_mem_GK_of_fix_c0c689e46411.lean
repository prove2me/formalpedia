-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_mem_GK_of_fix_c0c689e46411
-- name    : P2M_Formalism_BasicNotions_Examples__LB_mem_GK_of_fix_c0c689e46411
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:04:16.0145+00:00
-- url     : https://prove2.me/theorems/93cc4d12-a243-5297-8183-90714b3e71e6
-- title:
--   P2 M Formalism Basic Notions Examples  LB mem GK of fix c0c689e46411: P2 M Formalism Basic Notions Examples  LB mem GK of fix c0c689e46411
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB mem GK of fix c0c689e46411 construction uses the P2 M Formalism Basic Notions Examples  LB mem GK of fix c0c689e46411 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocB.lean#L61-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocB.lean#L61-L74

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

theorem P2M_Formalism_BasicNotions_Examples__LB_mem_GK_of_fix_c0c689e46411 (σ : GQ l) (h : ∀ x : E, σ (jE j x) = jE j x) :
    σ ∈ (KwF (E := E) j).fixingSubgroup := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«mem_GK_of_fix» := P2M_Formalism_BasicNotions_Examples__LB_mem_GK_of_fix_c0c689e46411
