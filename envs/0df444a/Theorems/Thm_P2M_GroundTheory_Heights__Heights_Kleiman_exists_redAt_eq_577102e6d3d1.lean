-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_redAt_eq_577102e6d3d1
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_redAt_eq_577102e6d3d1
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:07:26.542118+00:00
-- url     : https://prove2.me/theorems/b1de2c84-79c7-5d0c-8132-e29506b44adb
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists red At eq 577102e6d3d1: P2 M Ground Theory Heights  Heights Kleiman exists red At eq 577102e6d3d1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists red At eq 577102e6d3d1 construction uses the P2 M Ground Theory Heights  Heights Kleiman exists red At eq 577102e6d3d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L154-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionLocal.lean#L154-L158

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
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
variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} (x : Fin (N + 1) → Ω) (y : Fin (N + 1) → K')
variable {k x y}
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
include hsp

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_redAt_eq_577102e6d3d1 (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (I : Chart y) {c : K'}
    (hc : c ∈ chartRing k y I) : ∃ a ∈ chartRing k x (liftChart hxy I), redAt k x y a = c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_redAt_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_redAt_eq_577102e6d3d1
