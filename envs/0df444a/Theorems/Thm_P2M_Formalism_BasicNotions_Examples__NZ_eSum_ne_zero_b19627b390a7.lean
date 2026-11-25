-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_eSum_ne_zero_b19627b390a7
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_eSum_ne_zero_b19627b390a7
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:52:13.940802+00:00
-- url     : https://prove2.me/theorems/c9e0ac34-3eec-493e-a2cd-f8b596f4c2de
-- title:
--   P2 M Formalism Basic Notions Examples  NZ e Sum ne zero b19627b390a7: P2 M Formalism Basic Notions Examples  NZ e Sum ne zero b19627b390a7
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ e Sum ne zero b19627b390a7 construction uses the P2 M Formalism Basic Notions Examples  NZ e Sum ne zero b19627b390a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L134-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L134-L138

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
include hidem horth

theorem P2M_Formalism_BasicNotions_Examples__NZ_eSum_ne_zero_b19627b390a7 (b : ∀ i, L i) (hb : S b) (hne : ∀ i, E i (b i) ≠ 0) : eSum E S ≠ 0 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«eSum_ne_zero» := P2M_Formalism_BasicNotions_Examples__NZ_eSum_ne_zero_b19627b390a7
