-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twistRes_mem_e8907ed686b4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twistRes_mem_e8907ed686b4
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:26.098635+00:00
-- url     : https://prove2.me/theorems/b1b1704b-29d7-41aa-bc39-fd506fbed823
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Twist twist Res mem e8907ed686b4: P2 M Ground Theory Heights  Heights Kleiman Restrict Twist twist Res mem e8907ed686b4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Twist twist Res mem e8907ed686b4 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Twist twist Res mem e8907ed686b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L117-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L117-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twistRes_mem_e8907ed686b4 {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (c : ℤ) (I : Chart y) {q : Ω}
    (hq : q ∈ (twistSys S x c).sub (liftChart hxy I)) : twistRes S x y c q ∈ (twistSys S y c).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictTwist».«twistRes_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twistRes_mem_e8907ed686b4
