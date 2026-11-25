-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_esZ_sum_c28b4fa1c3ea
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_esZ_sum_c28b4fa1c3ea
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:04.986837+00:00
-- url     : https://prove2.me/theorems/607dc1fe-f49d-4acd-b88d-2301abbdec9a
-- title:
--   P2 M Formalism Basic Notions Examples  NZ es Z sum c28b4fa1c3ea: P2 M Formalism Basic Notions Examples  NZ es Z sum c28b4fa1c3ea
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ es Z sum c28b4fa1c3ea construction uses the P2 M Formalism Basic Notions Examples  NZ es Z sum c28b4fa1c3ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L176-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L176-L183

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeF
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
attribute [local instance] Classical.propDecidable
variable (K : Type) [Field K] (Γ : Type) {Λ : Type} [Group Γ] [Finite Γ] (fA fB : Λ)
variable {K Γ fA fB} [CharZero K] (hAB : fA ≠ fB)
omit [CharZero K]
include hAB

theorem P2M_Formalism_BasicNotions_Examples__NZ_esZ_sum_c28b4fa1c3ea (S : Finset Λ) (hA : fA ∈ S) (hB : fB ∈ S) : ∑ f ∈ S, esZ K Γ fA fB f = 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«esZ_sum» := P2M_Formalism_BasicNotions_Examples__NZ_esZ_sum_c28b4fa1c3ea
