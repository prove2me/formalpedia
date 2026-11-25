-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twistRes_eq_5dea7de76ecb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twistRes_eq_5dea7de76ecb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:09:50.810101+00:00
-- url     : https://prove2.me/theorems/da0254cd-274d-42f8-9290-674a5dc064cf
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Twist twist Res eq 5dea7de76ecb: P2 M Ground Theory Heights  Heights Kleiman Restrict Twist twist Res eq 5dea7de76ecb
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Twist twist Res eq 5dea7de76ecb construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Twist twist Res eq 5dea7de76ecb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L104-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L104-L115

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twistRes_eq_5dea7de76ecb {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) {c : ℤ} (I : Chart y) {z : Ω}
    {t : Poly S N × Poly S N × ℕ × ℕ} (h : IsFrac x c I.1 z t) :
    twistRes S x y c z = aeval y t.1 / aeval y t.2.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictTwist».«twistRes_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twistRes_eq_5dea7de76ecb
