-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_near_left_7dbeede3f3c6
-- name    : P2M_Formalism_BasicNotions_Examples__Tame_near_left_7dbeede3f3c6
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:53:21.99242+00:00
-- url     : https://prove2.me/theorems/b325250d-02dd-40b3-8a0c-cce85e1acdfc
-- title:
--   P2 M Formalism Basic Notions Examples  Tame near left 7dbeede3f3c6: P2 M Formalism Basic Notions Examples  Tame near left 7dbeede3f3c6
-- statement:
--   The P2 M Formalism Basic Notions Examples  Tame near left 7dbeede3f3c6 construction uses the P2 M Formalism Basic Notions Examples  Tame near left 7dbeede3f3c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L229-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L229-L230

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsTameGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.Tame
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
variable [IsAlgClosure E Ω]
attribute [instance] Test.grp Test.fin
omit [NumberField E] [IsAlgClosure E Ω]

theorem P2M_Formalism_BasicNotions_Examples__Tame_near_left_7dbeede3f3c6 {s t : Test E Ω} {σ : G E Ω} (h : Near A (s.prod t).φ σ) : Near A s.φ σ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«Tame».«near_left» := P2M_Formalism_BasicNotions_Examples__Tame_near_left_7dbeede3f3c6
