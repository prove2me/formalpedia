-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_eSum_central_56b4ffc8a854
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_eSum_central_56b4ffc8a854
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:52:49.126202+00:00
-- url     : https://prove2.me/theorems/62b0df1e-db7d-459a-a7f8-2b9c4e84498e
-- title:
--   P2 M Formalism Basic Notions Examples  NZ e Sum central 56b4ffc8a854: P2 M Formalism Basic Notions Examples  NZ e Sum central 56b4ffc8a854
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ e Sum central 56b4ffc8a854 construction uses the P2 M Formalism Basic Notions Examples  NZ e Sum central 56b4ffc8a854 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L87-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L87-L94

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
include hcen

theorem P2M_Formalism_BasicNotions_Examples__NZ_eSum_central_56b4ffc8a854 (a : MonoidAlgebra k (∀ i, G i)) : eSum E S * a = a * eSum E S := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«eSum_central» := P2M_Formalism_BasicNotions_Examples__NZ_eSum_central_56b4ffc8a854
