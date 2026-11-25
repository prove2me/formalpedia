-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_evS_esZ_ne_427e4833f6b3
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_evS_esZ_ne_427e4833f6b3
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:04:46.275479+00:00
-- url     : https://prove2.me/theorems/04eb9385-478f-4993-a947-06af762753c3
-- title:
--   P2 M Formalism Basic Notions Examples  NZ ev S es Z ne 427e4833f6b3: P2 M Formalism Basic Notions Examples  NZ ev S es Z ne 427e4833f6b3
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ ev S es Z ne 427e4833f6b3 construction uses the P2 M Formalism Basic Notions Examples  NZ ev S es Z ne 427e4833f6b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L198-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeF.lean#L198-L206

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
include hAB

theorem P2M_Formalism_BasicNotions_Examples__NZ_evS_esZ_ne_427e4833f6b3 (ψ : Γ →* K) (g : Γ) (hg : ψ g ≠ 1) (f : Λ) :
    evS ψ (esZ K Γ fA fB f) = if f = fA then 1 else 0 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«evS_esZ_ne» := P2M_Formalism_BasicNotions_Examples__NZ_evS_esZ_ne_427e4833f6b3
