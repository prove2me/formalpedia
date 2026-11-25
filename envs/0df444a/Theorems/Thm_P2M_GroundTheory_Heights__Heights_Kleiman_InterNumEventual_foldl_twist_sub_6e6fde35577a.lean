-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_foldl_twist_sub_6e6fde35577a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_foldl_twist_sub_6e6fde35577a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:51.519259+00:00
-- url     : https://prove2.me/theorems/8ea5e8e8-ac87-573a-a4ca-a9943e93cdbc
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual foldl twist sub 6e6fde35577a: P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual foldl twist sub 6e6fde35577a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual foldl twist sub 6e6fde35577a construction uses the P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual foldl twist sub 6e6fde35577a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumEventual.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumEventual.lean#L65-L72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumEventual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PRestrLenEuler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumEventual
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
open GroundTheory.Heights₂.Heights.Kleiman.InterNumEventual
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_foldl_twist_sub_6e6fde35577a {n : ℕ} (L : Fin n → SubSystem k x Ω) (I : Chart x) :
    ∀ (l : List (Fin n)) (F : SubSystem k x Ω),
      (l.foldl (fun F i => F.twist (L i)) F).sub I = F.sub I * (l.map fun i => (L i).sub I).prod
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«InterNumEventual».«foldl_twist_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_foldl_twist_sub_6e6fde35577a
