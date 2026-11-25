-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_jE_mem_86ded92f8610
-- name    : P2M_Formalism_BasicNotions_Examples__LB_jE_mem_86ded92f8610
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:06:04.368466+00:00
-- url     : https://prove2.me/theorems/0bab84f0-80e7-4a02-b67d-f94ce3eec261
-- title:
--   P2 M Formalism Basic Notions Examples  LB j E mem 86ded92f8610: P2 M Formalism Basic Notions Examples  LB j E mem 86ded92f8610
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB j E mem 86ded92f8610 construction uses the P2 M Formalism Basic Notions Examples  LB j E mem 86ded92f8610 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocB.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocB.lean#L20-L24

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

theorem P2M_Formalism_BasicNotions_Examples__LB_jE_mem_86ded92f8610 (x : E) : jE j x ∈ KwF (E := E) j := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«jE_mem» := P2M_Formalism_BasicNotions_Examples__LB_jE_mem_86ded92f8610
