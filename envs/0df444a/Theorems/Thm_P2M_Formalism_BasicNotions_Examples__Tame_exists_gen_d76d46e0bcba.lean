-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_exists_gen_d76d46e0bcba
-- name    : P2M_Formalism_BasicNotions_Examples__Tame_exists_gen_d76d46e0bcba
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:06:03.576913+00:00
-- url     : https://prove2.me/theorems/11353451-3966-5c91-9e71-1ca7142117bb
-- title:
--   P2 M Formalism Basic Notions Examples  Tame exists gen d76d46e0bcba: P2 M Formalism Basic Notions Examples  Tame exists gen d76d46e0bcba
-- statement:
--   The P2 M Formalism Basic Notions Examples  Tame exists gen d76d46e0bcba construction uses the P2 M Formalism Basic Notions Examples  Tame exists gen d76d46e0bcba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L136-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsTameGen.lean#L136-L212

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

theorem P2M_Formalism_BasicNotions_Examples__Tame_exists_gen_d76d46e0bcba (p : ℕ) (hp0 : p ≠ 0) (hp : A.valuation (p : Ω) < 1) (A' : Type) [Group A'] [Finite A']
    (φ : G E Ω →* A') (ho : IsOpen (φ.ker : Set (G E Ω))) :
    ∃ γ ∈ Ine (F := E) A, ∀ σ ∈ Ine (F := E) A, ∃ n : ℤ, Near A φ ((γ ^ n)⁻¹ * σ) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«Tame».«exists_gen» := P2M_Formalism_BasicNotions_Examples__Tame_exists_gen_d76d46e0bcba
