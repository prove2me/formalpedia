-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_Near_congr_94ffc6fcca87
-- name    : P2M_Formalism_BasicNotions_Examples__Tame_Near_congr_94ffc6fcca87
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:09:12.726627+00:00
-- url     : https://prove2.me/theorems/244b2559-fdfc-4c4d-a757-485e88bc8b6d
-- title:
--   P2 M Formalism Basic Notions Examples  Tame Near congr 94ffc6fcca87: P2 M Formalism Basic Notions Examples  Tame Near congr 94ffc6fcca87
-- statement:
--   The P2 M Formalism Basic Notions Examples  Tame Near congr 94ffc6fcca87 construction uses the P2 M Formalism Basic Notions Examples  Tame Near congr 94ffc6fcca87 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L128-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L128-L134

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
omit [NumberField E] [IsAlgClosure E Ω]

theorem P2M_Formalism_BasicNotions_Examples__Tame_Near_congr_94ffc6fcca87 {A' : Type} [Group A'] {φ : G E Ω →* A'} {σ σ' : G E Ω} (e : φ σ = φ σ')
    (h : Near A φ σ) : Near A φ σ' := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«Tame».«Near».«congr» := P2M_Formalism_BasicNotions_Examples__Tame_Near_congr_94ffc6fcca87
