-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_lift_ampleChart_5b828ba027de
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_lift_ampleChart_5b828ba027de
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:02:49.060475+00:00
-- url     : https://prove2.me/theorems/57bc7802-6852-4d09-8a6d-3a4435593130
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists lift ample Chart 5b828ba027de: P2 M Ground Theory Heights  Heights Kleiman exists lift ample Chart 5b828ba027de
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists lift ample Chart 5b828ba027de construction uses the P2 M Ground Theory Heights  Heights Kleiman exists lift ample Chart 5b828ba027de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L188-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L188-L204

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
  (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
  {Nb : LineBundle k x} {r : ℕ} {h : Fin (r + 1) → Ω}
include hsp
variable {g : Ω}
variable {σ : Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_lift_ampleChart_5b828ba027de (hg : RedGood hxy Nb.toSubSystem g) (Q' : LineBundle k y)
    (hQ : Q'.toSubSystem = redSys hxy Nb.toSubSystem g) (hσ : σ / g ∈ locAt k x y)
    (hσr : redAt k x y (σ / g) ≠ 0) (I : Chart y) {a : K'}
    (ha : a ∈ ampleChart Q'.toSubSystem 1 (redAt k x y (σ / g)) I) :
    ∃ e ∈ ampleChart Nb.toSubSystem 1 σ (liftChart hxy I), redAt k x y e = a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_lift_ampleChart» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_lift_ampleChart_5b828ba027de
