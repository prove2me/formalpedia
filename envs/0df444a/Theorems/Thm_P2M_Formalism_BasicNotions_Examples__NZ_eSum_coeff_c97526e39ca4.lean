-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_eSum_coeff_c97526e39ca4
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_eSum_coeff_c97526e39ca4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:56.736864+00:00
-- url     : https://prove2.me/theorems/8d534b8f-8d02-4a63-a15c-47038e254ef3
-- title:
--   P2 M Formalism Basic Notions Examples  NZ e Sum coeff c97526e39ca4: P2 M Formalism Basic Notions Examples  NZ e Sum coeff c97526e39ca4
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ e Sum coeff c97526e39ca4 construction uses the P2 M Formalism Basic Notions Examples  NZ e Sum coeff c97526e39ca4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L140-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean#L140-L148

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_eSum_coeff_c97526e39ca4 (g : ∀ i, G i) : (eSum E S).coeff g =
    open Classical in ∑ a : (∀ i, L i), if S a then ∏ i, (E i (a i)).coeff (g i) else 0 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«eSum_coeff» := P2M_Formalism_BasicNotions_Examples__NZ_eSum_coeff_c97526e39ca4
