-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exists_char_comm_1817172480b3
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_exists_char_comm_1817172480b3
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:52:28.172686+00:00
-- url     : https://prove2.me/theorems/512e0744-bd33-426d-8167-a9413ba0d66a
-- title:
--   P2 M Formalism Basic Notions Examples  NZ exists char comm 1817172480b3: P2 M Formalism Basic Notions Examples  NZ exists char comm 1817172480b3
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ exists char comm 1817172480b3 construction uses the P2 M Formalism Basic Notions Examples  NZ exists char comm 1817172480b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L150-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L150-L172

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open MonoidAlgebra
variable {k : Type} [Field k] {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
variable {L : I → Type} [∀ i, Fintype (L i)] [DecidableEq I] (E : ∀ i, L i → MonoidAlgebra k (G i))
  (S : (∀ i, L i) → Prop)
variable (hidem : ∀ i l, E i l * E i l = E i l) (hcen : ∀ i l a, E i l * a = a * E i l)
  (horth : ∀ i l l', l ≠ l' → E i l * E i l' = 0)

theorem P2M_Formalism_BasicNotions_Examples__NZ_exists_char_comm_1817172480b3 (Z : Type) [CommRing Z] [Algebra ℂ Z] [FiniteDimensional ℂ Z] (e : Z)
    (hi : e * e = e) (h0 : e ≠ 0) : ∃ ω : Z →ₐ[ℂ] ℂ, ω e = 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«exists_char_comm» := P2M_Formalism_BasicNotions_Examples__NZ_exists_char_comm_1817172480b3
