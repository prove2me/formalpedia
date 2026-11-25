-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_val_eq_210212283d05
-- name    : P2M_Formalism_BasicNotions_Examples__Tame_val_eq_210212283d05
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:03:59.105796+00:00
-- url     : https://prove2.me/theorems/2fe5f4fc-3c21-43b8-9993-489146037171
-- title:
--   P2 M Formalism Basic Notions Examples  Tame val eq 210212283d05: P2 M Formalism Basic Notions Examples  Tame val eq 210212283d05
-- statement:
--   The P2 M Formalism Basic Notions Examples  Tame val eq 210212283d05 construction uses the P2 M Formalism Basic Notions Examples  Tame val eq 210212283d05 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L50-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L50-L63

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

theorem P2M_Formalism_BasicNotions_Examples__Tame_val_eq_210212283d05 {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) (y : Ω) (hy : y ≠ 0) (N : ℕ) (hN : 0 < N)
    (hfix : ∀ z : ℤ, ∀ x, x = (σ ^ z) y → (σ ^ N) x = x) : A.valuation (σ y) = A.valuation y := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«Tame».«val_eq» := P2M_Formalism_BasicNotions_Examples__Tame_val_eq_210212283d05
