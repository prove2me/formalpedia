-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_iSup_span_secZ_eq_dc1f599cdd89
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_iSup_span_secZ_eq_dc1f599cdd89
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:09.919522+00:00
-- url     : https://prove2.me/theorems/6f175619-b625-4b5e-aa8d-c05383b36dc4
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq i Sup span sec Z eq dc1f599cdd89: P2 M Ground Theory Heights  Heights Kleiman Translate Eq i Sup span sec Z eq dc1f599cdd89
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq i Sup span sec Z eq dc1f599cdd89 construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq i Sup span sec Z eq dc1f599cdd89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistPowZeroSub.lean#L109-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistPowZeroSub.lean#L109-L133

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_iSup_span_secZ_eq_dc1f599cdd89 {r n : ℕ} (η : Fin (r + 1) → Ω) (bk : Fin n → ℕ) (s : Fin n → Ω) (b : ℕ) :
    (⨆ k, Submodule.span S (Set.image2 (· * ·) (IndefiniteRowSideFullHecke.Kleiman.secZ S η ((b : ℤ) - bk k) : Set Ω) {s k})) =
      Submodule.span S {z | ∃ (k : Fin n) (f : MvPolynomial (Fin (r + 1)) S) (e : ℕ), f.IsHomogeneous e ∧
        e + bk k = b ∧ z = aeval η f * s k} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«iSup_span_secZ_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_iSup_span_secZ_eq_dc1f599cdd89
