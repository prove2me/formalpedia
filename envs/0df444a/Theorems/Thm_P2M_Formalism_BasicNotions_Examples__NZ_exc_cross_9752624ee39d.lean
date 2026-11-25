-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exc_cross_9752624ee39d
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_exc_cross_9752624ee39d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:52:35.628714+00:00
-- url     : https://prove2.me/theorems/67702ec6-24cb-4f94-9ce0-0fa7b9b74cd7
-- title:
--   P2 M Formalism Basic Notions Examples  NZ exc cross 9752624ee39d: P2 M Formalism Basic Notions Examples  NZ exc cross 9752624ee39d
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ exc cross 9752624ee39d construction uses the P2 M Formalism Basic Notions Examples  NZ exc cross 9752624ee39d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeC.lean#L60-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeC.lean#L60-L69

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
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
open Polynomial Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]

theorem P2M_Formalism_BasicNotions_Examples__NZ_exc_cross_9752624ee39d {p s ℓ : ℕ} (hℓ : ℓ.Prime) (hp : 2 ≤ p) (hs : 1 ≤ s) (hc : Nat.Coprime p s)
    (u w : (Fbar g)ˣ) (hu : orderOf u = g ^ p - 1) (hw : orderOf w = g ^ s - 1) (i j c : ℕ)
    (h : ((u : Fbar g) ^ (g ^ i)) ^ (ℓ ^ c) = ((w : Fbar g) ^ (g ^ j)) ^ (ℓ ^ c)) : Exc g p ℓ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«exc_cross» := P2M_Formalism_BasicNotions_Examples__NZ_exc_cross_9752624ee39d
