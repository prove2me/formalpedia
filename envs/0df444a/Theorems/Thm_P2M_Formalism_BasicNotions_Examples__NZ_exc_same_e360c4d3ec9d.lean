-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exc_same_e360c4d3ec9d
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_exc_same_e360c4d3ec9d
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:52:36.208464+00:00
-- url     : https://prove2.me/theorems/129adea8-fe85-4296-88b3-a1584850e981
-- title:
--   P2 M Formalism Basic Notions Examples  NZ exc same e360c4d3ec9d: P2 M Formalism Basic Notions Examples  NZ exc same e360c4d3ec9d
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ exc same e360c4d3ec9d construction uses the P2 M Formalism Basic Notions Examples  NZ exc same e360c4d3ec9d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeC.lean#L36-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeC.lean#L36-L56

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_exc_same_e360c4d3ec9d {ℓ : ℕ} (hℓ : ℓ.Prime) {i j c : ℕ} (hi : i < d) (hj : j < d) (hij : i ≠ j)
    (h : ((u : Fbar g) ^ (g ^ i)) ^ (ℓ ^ c) = ((u : Fbar g) ^ (g ^ j)) ^ (ℓ ^ c)) : Exc g d ℓ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«exc_same» := P2M_Formalism_BasicNotions_Examples__NZ_exc_same_e360c4d3ec9d
