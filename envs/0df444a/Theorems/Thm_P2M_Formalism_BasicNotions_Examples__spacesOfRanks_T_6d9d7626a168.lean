-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__spacesOfRanks_T_6d9d7626a168
-- name    : P2M_Formalism_BasicNotions_Examples__spacesOfRanks_T_6d9d7626a168
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:06:01.616216+00:00
-- url     : https://prove2.me/theorems/24c7fc04-f207-5fd7-8701-c1d6a0c8bc5c
-- title:
--   P2 M Formalism Basic Notions Examples  spaces Of Ranks T 6d9d7626a168: P2 M Formalism Basic Notions Examples  spaces Of Ranks T 6d9d7626a168
-- statement:
--   The P2 M Formalism Basic Notions Examples  spaces Of Ranks T 6d9d7626a168 construction uses the P2 M Formalism Basic Notions Examples  spaces Of Ranks T 6d9d7626a168 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/BaseFormAnisotropicOrthogonalSingle.lean#L388-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/BaseFormAnisotropicOrthogonalSingle.lean#L388-L388

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_BaseFormAnisotropicOrthogonalSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open NumberField IsDedekindDomain
open scoped TensorProduct
variable (R : Ranks) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E]
  (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
  (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)
  (hy : ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1)

theorem P2M_Formalism_BasicNotions_Examples__spacesOfRanks_T_6d9d7626a168 : (spacesOfRanks R hstar cm T hT pz hpz hy).T = T := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«spacesOfRanks_T» := P2M_Formalism_BasicNotions_Examples__spacesOfRanks_T_6d9d7626a168
