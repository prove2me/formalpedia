-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_one_sub_eT_ne_zero_d011cad6a312
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_one_sub_eT_ne_zero_d011cad6a312
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:54:38.310179+00:00
-- url     : https://prove2.me/theorems/70b1a80c-a7eb-56e6-9189-2e8c0a101958
-- title:
--   P2 M Formalism Basic Notions Examples  NZ one sub e T ne zero d011cad6a312: P2 M Formalism Basic Notions Examples  NZ one sub e T ne zero d011cad6a312
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ one sub e T ne zero d011cad6a312 construction uses the P2 M Formalism Basic Notions Examples  NZ one sub e T ne zero d011cad6a312 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L109-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L109-L113

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
variable (K : Type) [Field K] (Γ : Type) [Group Γ] [Finite Γ]
variable {K Γ}

theorem P2M_Formalism_BasicNotions_Examples__NZ_one_sub_eT_ne_zero_d011cad6a312 [CharZero K] (g : Γ) (hg : g ≠ 1) : 1 - eT K Γ ≠ 0 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«one_sub_eT_ne_zero» := P2M_Formalism_BasicNotions_Examples__NZ_one_sub_eT_ne_zero_d011cad6a312
