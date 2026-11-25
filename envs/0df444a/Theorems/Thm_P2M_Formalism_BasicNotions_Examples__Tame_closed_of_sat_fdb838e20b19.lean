-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_closed_of_sat_fdb838e20b19
-- name    : P2M_Formalism_BasicNotions_Examples__Tame_closed_of_sat_fdb838e20b19
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:53:20.450958+00:00
-- url     : https://prove2.me/theorems/7bab2ee8-9ed2-4864-b8f9-917eaf445496
-- title:
--   P2 M Formalism Basic Notions Examples  Tame closed of sat fdb838e20b19: P2 M Formalism Basic Notions Examples  Tame closed of sat fdb838e20b19
-- statement:
--   The P2 M Formalism Basic Notions Examples  Tame closed of sat fdb838e20b19 construction uses the P2 M Formalism Basic Notions Examples  Tame closed of sat fdb838e20b19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L237-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L237-L248

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

theorem P2M_Formalism_BasicNotions_Examples__Tame_closed_of_sat_fdb838e20b19 (t : Test E Ω) (X : Set (G E Ω))
    (h : ∀ σ σ', t.φ σ = t.φ σ' → σ ∈ X → σ' ∈ X) : IsClosed X := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«Tame».«closed_of_sat» := P2M_Formalism_BasicNotions_Examples__Tame_closed_of_sat_fdb838e20b19
