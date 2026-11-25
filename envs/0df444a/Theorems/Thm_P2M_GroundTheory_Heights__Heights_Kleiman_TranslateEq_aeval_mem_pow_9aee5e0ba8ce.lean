-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_aeval_mem_pow_9aee5e0ba8ce
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_aeval_mem_pow_9aee5e0ba8ce
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:29:11.669574+00:00
-- url     : https://prove2.me/theorems/72a8c1f5-d091-45a6-beab-cf9ba735f6a7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq aeval mem pow 9aee5e0ba8ce: P2 M Ground Theory Heights  Heights Kleiman Translate Eq aeval mem pow 9aee5e0ba8ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq aeval mem pow 9aee5e0ba8ce construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq aeval mem pow 9aee5e0ba8ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistPowZeroSub.lean#L135-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistPowZeroSub.lean#L135-L156

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NotTwistFiniteAtZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistPowZeroSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_aeval_mem_pow_9aee5e0ba8ce {r : ℕ} {Q : Submodule S Ω} {η : Fin (r + 1) → Ω} (hη : ∀ j, η j ∈ Q)
    {f : MvPolynomial (Fin (r + 1)) S} {e : ℕ} (hf : f.IsHomogeneous e) : aeval η f ∈ Q ^ e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«aeval_mem_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_aeval_mem_pow_9aee5e0ba8ce
