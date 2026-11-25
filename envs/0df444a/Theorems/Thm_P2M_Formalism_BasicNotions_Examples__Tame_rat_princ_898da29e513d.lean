-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_rat_princ_898da29e513d
-- name    : P2M_Formalism_BasicNotions_Examples__Tame_rat_princ_898da29e513d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:53:40.302949+00:00
-- url     : https://prove2.me/theorems/650c9662-d0e4-4a68-9d20-cc3e9cdd2e35
-- title:
--   P2 M Formalism Basic Notions Examples  Tame rat princ 898da29e513d: P2 M Formalism Basic Notions Examples  Tame rat princ 898da29e513d
-- statement:
--   The P2 M Formalism Basic Notions Examples  Tame rat princ 898da29e513d construction uses the P2 M Formalism Basic Notions Examples  Tame rat princ 898da29e513d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L24-L27

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

theorem P2M_Formalism_BasicNotions_Examples__Tame_rat_princ_898da29e513d {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (u : Ωˣ) (hu : A.valuation u = 1) :
    rat σ u ∈ A.principalUnitGroup := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«Tame».«rat_princ» := P2M_Formalism_BasicNotions_Examples__Tame_rat_princ_898da29e513d
