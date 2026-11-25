-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_pow_primeToPart_f231a455406b
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_pow_primeToPart_f231a455406b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:45.231779+00:00
-- url     : https://prove2.me/theorems/86c834b1-d517-4120-a990-0e85cf446c7a
-- title:
--   P2 M Formalism Basic Notions Examples  NZ pow prime To Part f231a455406b: P2 M Formalism Basic Notions Examples  NZ pow prime To Part f231a455406b
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ pow prime To Part f231a455406b construction uses the P2 M Formalism Basic Notions Examples  NZ pow prime To Part f231a455406b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeA.lean#L11-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeA.lean#L11-L33

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_pow_primeToPart_f231a455406b {M : Type*} [Monoid M] {ℓ : ℕ} (hℓ : ℓ.Prime) (x : M) (hx : IsOfFinOrder x) :
    primeToPart ℓ x ^ (ℓ ^ (orderOf x).factorization ℓ) = x ^ (ℓ ^ (orderOf x).factorization ℓ) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«pow_primeToPart» := P2M_Formalism_BasicNotions_Examples__NZ_pow_primeToPart_f231a455406b
