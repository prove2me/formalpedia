-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_exists_test_5e3aaaee6b64
-- name    : P2M_Formalism_BasicNotions_Examples__Tame_exists_test_5e3aaaee6b64
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:15:03.421059+00:00
-- url     : https://prove2.me/theorems/c5f25da3-31ef-5f73-9f75-2d6f68c1dd3c
-- title:
--   P2 M Formalism Basic Notions Examples  Tame exists test 5e3aaaee6b64: P2 M Formalism Basic Notions Examples  Tame exists test 5e3aaaee6b64
-- statement:
--   The P2 M Formalism Basic Notions Examples  Tame exists test 5e3aaaee6b64 construction uses the P2 M Formalism Basic Notions Examples  Tame exists test 5e3aaaee6b64 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L250-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L250-L258

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

theorem P2M_Formalism_BasicNotions_Examples__Tame_exists_test_5e3aaaee6b64 (y : Ω) : ∃ t : Test E Ω, ∀ κ ∈ t.φ.ker, κ y = y := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«Tame».«exists_test» := P2M_Formalism_BasicNotions_Examples__Tame_exists_test_5e3aaaee6b64
