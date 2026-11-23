-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_dvd_of_pow_eq_7b799bd31cc9
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_dvd_of_pow_eq_7b799bd31cc9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:25.156619+00:00
-- url     : https://prove2.me/theorems/59b33834-bf9b-484b-95b4-3ce6d5e99093
-- title:
--   P2 M Formalism Basic Notions Examples  NZ dvd of pow eq 7b799bd31cc9: P2 M Formalism Basic Notions Examples  NZ dvd of pow eq 7b799bd31cc9
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ dvd of pow eq 7b799bd31cc9 construction uses the P2 M Formalism Basic Notions Examples  NZ dvd of pow eq 7b799bd31cc9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L53-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L53-L66

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
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

theorem P2M_Formalism_BasicNotions_Examples__NZ_dvd_of_pow_eq_7b799bd31cc9 {i j a : ℕ} (hij : i ≤ j) (h : u ^ (g ^ i * a) = u ^ (g ^ j * a)) :
    g ^ d - 1 ∣ a * (g ^ (j - i) - 1) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«dvd_of_pow_eq» := P2M_Formalism_BasicNotions_Examples__NZ_dvd_of_pow_eq_7b799bd31cc9
