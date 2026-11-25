-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_exists_tameGen_8cf65168770b
-- name    : P2M_Formalism_BasicNotions_Examples__Tame_exists_tameGen_8cf65168770b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:54:07.363794+00:00
-- url     : https://prove2.me/theorems/f3f82ea6-a4fc-4a1a-97f1-77dd75a345c7
-- title:
--   P2 M Formalism Basic Notions Examples  Tame exists tame Gen 8cf65168770b: P2 M Formalism Basic Notions Examples  Tame exists tame Gen 8cf65168770b
-- statement:
--   The P2 M Formalism Basic Notions Examples  Tame exists tame Gen 8cf65168770b construction uses the P2 M Formalism Basic Notions Examples  Tame exists tame Gen 8cf65168770b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L260-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L260-L293

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

theorem P2M_Formalism_BasicNotions_Examples__Tame_exists_tameGen_8cf65168770b (p : ℕ) (hp0 : p ≠ 0) (hp : A.valuation (p : Ω) < 1) :
    ∃ γ : G E Ω, TameGenAt A γ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«Tame».«exists_tameGen» := P2M_Formalism_BasicNotions_Examples__Tame_exists_tameGen_8cf65168770b
