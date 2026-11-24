-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_val_nat_eq_one_5b47ed1a4a71
-- name    : P2M_Formalism_BasicNotions_Examples__Tame_val_nat_eq_one_5b47ed1a4a71
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:48:48.448578+00:00
-- url     : https://prove2.me/theorems/5c83232d-2187-4ff2-8ee3-861f8d6e66a3
-- title:
--   P2 M Formalism Basic Notions Examples  Tame val nat eq one 5b47ed1a4a71: P2 M Formalism Basic Notions Examples  Tame val nat eq one 5b47ed1a4a71
-- statement:
--   The P2 M Formalism Basic Notions Examples  Tame val nat eq one 5b47ed1a4a71 construction uses the P2 M Formalism Basic Notions Examples  Tame val nat eq one 5b47ed1a4a71 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L65-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L65-L77

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

theorem P2M_Formalism_BasicNotions_Examples__Tame_val_nat_eq_one_5b47ed1a4a71 (p N : ℕ) (hp : A.valuation (p : Ω) < 1) (hc : N.Coprime p) :
    A.valuation (N : Ω) = 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«Tame».«val_nat_eq_one» := P2M_Formalism_BasicNotions_Examples__Tame_val_nat_eq_one_5b47ed1a4a71
