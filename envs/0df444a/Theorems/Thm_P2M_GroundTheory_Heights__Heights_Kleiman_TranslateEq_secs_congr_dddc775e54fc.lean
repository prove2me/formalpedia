-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_congr_dddc775e54fc
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_congr_dddc775e54fc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:16.5018+00:00
-- url     : https://prove2.me/theorems/503a0e46-7540-4642-a9d2-517b6da338f7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq secs congr dddc775e54fc: P2 M Ground Theory Heights  Heights Kleiman Translate Eq secs congr dddc775e54fc
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq secs congr dddc775e54fc construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq secs congr dddc775e54fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistPowZeroSub.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistPowZeroSub.lean#L14-L17

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_congr_dddc775e54fc {F F' : Fin (N + 1) → Submodule S Ω} (h : ∀ i, x i ≠ 0 → F i = F' i) :
    IndefiniteRowSideFullHecke.Kleiman.secs S x F = IndefiniteRowSideFullHecke.Kleiman.secs S x F' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«secs_congr» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_congr_dddc775e54fc
