-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_coprime_n_8914bd4d6568
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_coprime_n_8914bd4d6568
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:50:44.558569+00:00
-- url     : https://prove2.me/theorems/a70dc0ba-edf9-4f6c-bd02-444775ebb4d2
-- title:
--   P2 M Formalism Basic Notions Examples  NZ coprime n 8914bd4d6568: P2 M Formalism Basic Notions Examples  NZ coprime n 8914bd4d6568
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ coprime n 8914bd4d6568 construction uses the P2 M Formalism Basic Notions Examples  NZ coprime n 8914bd4d6568 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean#L15-L24

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_coprime_n_8914bd4d6568 (d : ℕ) (hd : 1 ≤ d) : Nat.Coprime (g ^ d - 1) g := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«coprime_n» := P2M_Formalism_BasicNotions_Examples__NZ_coprime_n_8914bd4d6568
