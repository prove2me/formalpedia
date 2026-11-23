-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_one_lt_pow_g_0b14e5602731
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_one_lt_pow_g_0b14e5602731
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:50:37.606875+00:00
-- url     : https://prove2.me/theorems/015c56d0-8e2e-4bfd-916e-0d647acfe4d6
-- title:
--   P2 M Formalism Basic Notions Examples  NZ one lt pow g 0b14e5602731: P2 M Formalism Basic Notions Examples  NZ one lt pow g 0b14e5602731
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ one lt pow g 0b14e5602731 construction uses the P2 M Formalism Basic Notions Examples  NZ one lt pow g 0b14e5602731 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L11-L13

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_one_lt_pow_g_0b14e5602731 {d : ℕ} (hd : 1 ≤ d) : 2 ≤ g ^ d := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«one_lt_pow_g» := P2M_Formalism_BasicNotions_Examples__NZ_one_lt_pow_g_0b14e5602731
