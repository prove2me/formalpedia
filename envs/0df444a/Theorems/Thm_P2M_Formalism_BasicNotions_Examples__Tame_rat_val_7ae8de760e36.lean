-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_rat_val_7ae8de760e36
-- name    : P2M_Formalism_BasicNotions_Examples__Tame_rat_val_7ae8de760e36
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:51:25.423515+00:00
-- url     : https://prove2.me/theorems/5506289d-fc69-471b-8784-3bbba10f9523
-- title:
--   P2 M Formalism Basic Notions Examples  Tame rat val 7ae8de760e36: P2 M Formalism Basic Notions Examples  Tame rat val 7ae8de760e36
-- statement:
--   The P2 M Formalism Basic Notions Examples  Tame rat val 7ae8de760e36 construction uses the P2 M Formalism Basic Notions Examples  Tame rat val 7ae8de760e36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L13-L14

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

theorem P2M_Formalism_BasicNotions_Examples__Tame_rat_val_7ae8de760e36 (σ : G E Ω) (y : Ωˣ) : ((rat σ y : Ωˣ) : Ω) = σ y / y := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«Tame».«rat_val» := P2M_Formalism_BasicNotions_Examples__Tame_rat_val_7ae8de760e36
