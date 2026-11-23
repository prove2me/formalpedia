-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_eSum_mul_tens_1693cea8da2a
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_eSum_mul_tens_1693cea8da2a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:32.941935+00:00
-- url     : https://prove2.me/theorems/0d9381dd-c370-4afe-8c1b-f94aa96dc6c4
-- title:
--   P2 M Formalism Basic Notions Examples  NZ e Sum mul tens 1693cea8da2a: P2 M Formalism Basic Notions Examples  NZ e Sum mul tens 1693cea8da2a
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ e Sum mul tens 1693cea8da2a construction uses the P2 M Formalism Basic Notions Examples  NZ e Sum mul tens 1693cea8da2a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L106-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L106-L118

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_eSum_mul_tens_1693cea8da2a (b : ∀ i, L i) : eSum E S * tens (fun i => E i (b i)) =
    open Classical in if S b then tens (fun i => E i (b i)) else 0 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«eSum_mul_tens» := P2M_Formalism_BasicNotions_Examples__NZ_eSum_mul_tens_1693cea8da2a
