-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_card_ne_cf5bb1f9180d
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_card_ne_cf5bb1f9180d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:52:58.125968+00:00
-- url     : https://prove2.me/theorems/6a111213-100b-5cc4-91b9-803325cfd935
-- title:
--   P2 M Formalism Basic Notions Examples  NZ card ne cf5bb1f9180d: P2 M Formalism Basic Notions Examples  NZ card ne cf5bb1f9180d
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ card ne cf5bb1f9180d construction uses the P2 M Formalism Basic Notions Examples  NZ card ne cf5bb1f9180d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L90-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L90-L90

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

theorem P2M_Formalism_BasicNotions_Examples__NZ_card_ne_cf5bb1f9180d [CharZero K] : (Nat.card Γ : K) ≠ 0 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«card_ne» := P2M_Formalism_BasicNotions_Examples__NZ_card_ne_cf5bb1f9180d
