-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exists_char_2fc1fe4faba6
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_exists_char_2fc1fe4faba6
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:02.132821+00:00
-- url     : https://prove2.me/theorems/60ed8b29-082d-4207-a296-ac93ea602d0f
-- title:
--   P2 M Formalism Basic Notions Examples  NZ exists char 2fc1fe4faba6: P2 M Formalism Basic Notions Examples  NZ exists char 2fc1fe4faba6
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ exists char 2fc1fe4faba6 construction uses the P2 M Formalism Basic Notions Examples  NZ exists char 2fc1fe4faba6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L174-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L174-L179

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_exists_char_2fc1fe4faba6 {Γ : Type} [Group Γ] [Finite Γ] (e : MonoidAlgebra ℂ Γ)
    (hc : e ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ Γ)) (hi : e * e = e) (h0 : e ≠ 0) :
    ∃ ω : Subalgebra.center ℂ (MonoidAlgebra ℂ Γ) →ₐ[ℂ] ℂ, ω ⟨e, hc⟩ = 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«exists_char» := P2M_Formalism_BasicNotions_Examples__NZ_exists_char_2fc1fe4faba6
