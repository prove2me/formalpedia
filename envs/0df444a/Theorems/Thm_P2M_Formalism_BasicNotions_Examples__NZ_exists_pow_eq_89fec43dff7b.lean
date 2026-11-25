-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exists_pow_eq_89fec43dff7b
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_exists_pow_eq_89fec43dff7b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:53:49.629615+00:00
-- url     : https://prove2.me/theorems/d6b4c2b2-7781-415c-95f2-ed1be0158bf1
-- title:
--   P2 M Formalism Basic Notions Examples  NZ exists pow eq 89fec43dff7b: P2 M Formalism Basic Notions Examples  NZ exists pow eq 89fec43dff7b
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ exists pow eq 89fec43dff7b construction uses the P2 M Formalism Basic Notions Examples  NZ exists pow eq 89fec43dff7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeA.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeA.lean#L35-L40

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
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
open Polynomial Formalism.CyclotomicNorms

theorem P2M_Formalism_BasicNotions_Examples__NZ_exists_pow_eq_89fec43dff7b {M : Type*} [Monoid M] {ℓ : ℕ} (hℓ : ℓ.Prime) (x y : M) (hx : IsOfFinOrder x)
    (hy : IsOfFinOrder y) (h : primeToPart ℓ x = primeToPart ℓ y) : ∃ c : ℕ, x ^ ℓ ^ c = y ^ ℓ ^ c := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«exists_pow_eq» := P2M_Formalism_BasicNotions_Examples__NZ_exists_pow_eq_89fec43dff7b
