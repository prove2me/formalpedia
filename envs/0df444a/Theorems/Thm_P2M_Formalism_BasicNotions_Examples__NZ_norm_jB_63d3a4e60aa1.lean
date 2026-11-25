-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_norm_jB_63d3a4e60aa1
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_norm_jB_63d3a4e60aa1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:04.037715+00:00
-- url     : https://prove2.me/theorems/a3047d91-d234-4f88-9b78-39b102921f25
-- title:
--   P2 M Formalism Basic Notions Examples  NZ norm j B 63d3a4e60aa1: P2 M Formalism Basic Notions Examples  NZ norm j B 63d3a4e60aa1
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ norm j B 63d3a4e60aa1 construction uses the P2 M Formalism Basic Notions Examples  NZ norm j B 63d3a4e60aa1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L106-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean#L106-L108

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA
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
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)

theorem P2M_Formalism_BasicNotions_Examples__NZ_norm_jB_63d3a4e60aa1 (x : Fin n → K) : ‖jB σ b x‖ = Real.sqrt (∑ i, ‖σ (x i)‖ ^ 2) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«norm_jB» := P2M_Formalism_BasicNotions_Examples__NZ_norm_jB_63d3a4e60aa1
