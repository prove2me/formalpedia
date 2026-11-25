-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_esZ_orth_08f376ba39d3
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_esZ_orth_08f376ba39d3
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:56:16.352374+00:00
-- url     : https://prove2.me/theorems/f67bd004-5654-4546-8d0d-750b1e8940a6
-- title:
--   P2 M Formalism Basic Notions Examples  NZ es Z orth 08f376ba39d3: P2 M Formalism Basic Notions Examples  NZ es Z orth 08f376ba39d3
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ es Z orth 08f376ba39d3 construction uses the P2 M Formalism Basic Notions Examples  NZ es Z orth 08f376ba39d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L164-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L164-L172

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_esZ_orth_08f376ba39d3 (f f' : Λ) (h : f ≠ f') : esZ K Γ fA fB f * esZ K Γ fA fB f' = 0 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«esZ_orth» := P2M_Formalism_BasicNotions_Examples__NZ_esZ_orth_08f376ba39d3
