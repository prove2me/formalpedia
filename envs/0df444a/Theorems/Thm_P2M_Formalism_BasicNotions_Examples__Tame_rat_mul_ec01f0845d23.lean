-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_rat_mul_ec01f0845d23
-- name    : P2M_Formalism_BasicNotions_Examples__Tame_rat_mul_ec01f0845d23
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:53:54.013869+00:00
-- url     : https://prove2.me/theorems/3e661bed-67e9-4bf9-8f28-22c9bd01f91b
-- title:
--   P2 M Formalism Basic Notions Examples  Tame rat mul ec01f0845d23: P2 M Formalism Basic Notions Examples  Tame rat mul ec01f0845d23
-- statement:
--   The P2 M Formalism Basic Notions Examples  Tame rat mul ec01f0845d23 construction uses the P2 M Formalism Basic Notions Examples  Tame rat mul ec01f0845d23 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L16-L22

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

theorem P2M_Formalism_BasicNotions_Examples__Tame_rat_mul_ec01f0845d23 (σ τ : G E Ω) (y : Ωˣ) : rat (σ * τ) y = rat σ (rat τ y) * rat τ y * rat σ y := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«Tame».«rat_mul» := P2M_Formalism_BasicNotions_Examples__Tame_rat_mul_ec01f0845d23
