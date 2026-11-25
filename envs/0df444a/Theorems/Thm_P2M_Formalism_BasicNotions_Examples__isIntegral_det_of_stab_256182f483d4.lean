-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__isIntegral_det_of_stab_256182f483d4
-- name    : P2M_Formalism_BasicNotions_Examples__isIntegral_det_of_stab_256182f483d4
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:14.598995+00:00
-- url     : https://prove2.me/theorems/fb2df7c8-958c-47ea-ab56-76fc54725598
-- title:
--   P2 M Formalism Basic Notions Examples  is Integral det of stab 256182f483d4: P2 M Formalism Basic Notions Examples  is Integral det of stab 256182f483d4
-- statement:
--   The P2 M Formalism Basic Notions Examples  is Integral det of stab 256182f483d4 construction uses the P2 M Formalism Basic Notions Examples  is Integral det of stab 256182f483d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/RelDetCore.lean#L109-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/RelDetCore.lean#L109-L117

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

theorem P2M_Formalism_BasicNotions_Examples__isIntegral_det_of_stab_256182f483d4 (γ : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤)
    (hγ : ∀ x ∈ L, γ.mulVec x ∈ L) : IsIntegral ℤ γ.det := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«isIntegral_det_of_stab» := P2M_Formalism_BasicNotions_Examples__isIntegral_det_of_stab_256182f483d4
