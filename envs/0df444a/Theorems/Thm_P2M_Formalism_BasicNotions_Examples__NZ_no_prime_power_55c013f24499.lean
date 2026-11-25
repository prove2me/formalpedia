-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_no_prime_power_55c013f24499
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_no_prime_power_55c013f24499
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:47.874945+00:00
-- url     : https://prove2.me/theorems/01436477-8167-4063-b23c-d121defd30f8
-- title:
--   P2 M Formalism Basic Notions Examples  NZ no prime power 55c013f24499: P2 M Formalism Basic Notions Examples  NZ no prime power 55c013f24499
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ no prime power 55c013f24499 construction uses the P2 M Formalism Basic Notions Examples  NZ no prime power 55c013f24499 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeC.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeC.lean#L23-L33

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
variable {d : ℕ} (hd : 1 ≤ d) (u : (Fbar g)ˣ) (hu : orderOf u = g ^ d - 1)
include hd hu

theorem P2M_Formalism_BasicNotions_Examples__NZ_no_prime_power_55c013f24499 {q0 ℓ : ℕ} (hℓ : ℓ.Prime) (hq0 : q0.Prime) (hq2 : q0 ≠ 2) (h2g : 2 ∣ g - 1)
    (hqg : q0 ∣ g - 1) (i c : ℕ) : ((u : Fbar g) ^ (g ^ i)) ^ (ℓ ^ c) ≠ 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«no_prime_power» := P2M_Formalism_BasicNotions_Examples__NZ_no_prime_power_55c013f24499
