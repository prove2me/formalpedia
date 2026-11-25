-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__det_root_of_unity_of_stab_bbf976f1d2c5
-- name    : P2M_Formalism_BasicNotions_Examples__det_root_of_unity_of_stab_bbf976f1d2c5
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:22.3618+00:00
-- url     : https://prove2.me/theorems/c2746ced-79a7-4daa-b3e4-6a153b49e71a
-- title:
--   P2 M Formalism Basic Notions Examples  det root of unity of stab bbf976f1d2c5: P2 M Formalism Basic Notions Examples  det root of unity of stab bbf976f1d2c5
-- statement:
--   The P2 M Formalism Basic Notions Examples  det root of unity of stab bbf976f1d2c5 construction uses the P2 M Formalism Basic Notions Examples  det root of unity of stab bbf976f1d2c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/RelDetCore.lean#L119-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/RelDetCore.lean#L119-L139

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

theorem P2M_Formalism_BasicNotions_Examples__det_root_of_unity_of_stab_bbf976f1d2c5 [StarRing E]
    (hstar : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    (γ : Matrix (Fin N) (Fin N) E) (hu : γ.det ∈ unitary E) (L : Submodule (𝓞 E) (Fin N → E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤)
    (hγ : ∀ x ∈ L, γ.mulVec x ∈ L) : ∃ n : ℕ, 0 < n ∧ γ.det ^ n = 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«det_root_of_unity_of_stab» := P2M_Formalism_BasicNotions_Examples__det_root_of_unity_of_stab_bbf976f1d2c5
