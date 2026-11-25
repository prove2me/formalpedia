-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__detIdeal_smul_96d231c920a3
-- name    : P2M_Formalism_BasicNotions_Examples__detIdeal_smul_96d231c920a3
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:07.585259+00:00
-- url     : https://prove2.me/theorems/298e4a51-5cb3-4168-9058-cab8d05cfc8a
-- title:
--   P2 M Formalism Basic Notions Examples  det Ideal smul 96d231c920a3: P2 M Formalism Basic Notions Examples  det Ideal smul 96d231c920a3
-- statement:
--   The P2 M Formalism Basic Notions Examples  det Ideal smul 96d231c920a3 construction uses the P2 M Formalism Basic Notions Examples  det Ideal smul 96d231c920a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/RelDetCore.lean#L27-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/RelDetCore.lean#L27-L37

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_RelDetCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
variable {E : Type*} [Field E] [NumberField E] {N : ℕ}

theorem P2M_Formalism_BasicNotions_Examples__detIdeal_smul_96d231c920a3 (γ : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E))
    (hγ : ∀ x ∈ L, γ.mulVec x ∈ L) : ∀ n ∈ detIdeal L, γ.det • n ∈ detIdeal L := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«detIdeal_smul» := P2M_Formalism_BasicNotions_Examples__detIdeal_smul_96d231c920a3
