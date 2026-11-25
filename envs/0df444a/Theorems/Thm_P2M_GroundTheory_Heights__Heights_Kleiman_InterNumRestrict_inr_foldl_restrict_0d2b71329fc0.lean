-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumRestrict_inr_foldl_restrict_0d2b71329fc0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_InterNumRestrict_inr_foldl_restrict_0d2b71329fc0
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:56:44.672425+00:00
-- url     : https://prove2.me/theorems/37ce6b76-deef-42b8-bd74-08f97655360b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Inter Num Restrict inr foldl restrict 0d2b71329fc0: P2 M Ground Theory Heights  Heights Kleiman Inter Num Restrict inr foldl restrict 0d2b71329fc0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Inter Num Restrict inr foldl restrict 0d2b71329fc0 construction uses the P2 M Ground Theory Heights  Heights Kleiman Inter Num Restrict inr foldl restrict 0d2b71329fc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PInterNumRestrict.lean#L21-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PInterNumRestrict.lean#L21-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PInterNumRestrict
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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.InterNumRestrict
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {K' : Type w} [Field K'] [Algebra k K'] {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_InterNumRestrict_inr_foldl_restrict_0d2b71329fc0 {n : ℕ} (L : Fin n → LineBundle k x) (L' : Fin n → LineBundle k y)
    (rr : Fin n → Ω → K') (hL : ∀ i, RestrictData (L i).toSubSystem hxy (L' i).toSubSystem (rr i)) :
    ∀ (l : List (Fin n)) (Q : LineBundle k x) (Q' : LineBundle k y) (r : Ω → K'),
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r →
      ∃ (P : LineBundle k x) (P' : LineBundle k y) (s : Ω → K'),
        l.foldl (fun F i => F.twist (L i).toSubSystem) Q.toSubSystem = P.toSubSystem ∧
        l.foldl (fun F i => F.twist (L' i).toSubSystem) Q'.toSubSystem = P'.toSubSystem ∧
        RestrictData P.toSubSystem hxy P'.toSubSystem s
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«InterNumRestrict».«inr_foldl_restrict» := P2M_GroundTheory_Heights__Heights_Kleiman_InterNumRestrict_inr_foldl_restrict_0d2b71329fc0
