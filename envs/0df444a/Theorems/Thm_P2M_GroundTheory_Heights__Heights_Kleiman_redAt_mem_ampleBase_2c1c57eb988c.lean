-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redAt_mem_ampleBase_2c1c57eb988c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_redAt_mem_ampleBase_2c1c57eb988c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:12:43.445428+00:00
-- url     : https://prove2.me/theorems/5d82b9e6-ee4f-4e36-9597-21a1fdee4442
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman red At mem ample Base 2c1c57eb988c: P2 M Ground Theory Heights  Heights Kleiman red At mem ample Base 2c1c57eb988c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman red At mem ample Base 2c1c57eb988c construction uses the P2 M Ground Theory Heights  Heights Kleiman red At mem ample Base 2c1c57eb988c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L206-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L206-L225

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_redAt_mem_ampleBase_2c1c57eb988c (hg0 : g ≠ 0) (hgl : ∀ l, h l / g ∈ locAt k x y) {j : Fin (r + 1)}
    (hr : redAt k x y (h j / g) ≠ 0) {z : Ω} (hz : z ∈ ampleBase (S := k) h j) :
    z ∈ locAt k x y ∧
      redAt k x y z ∈ ampleBase (S := k) (fun l => redAt k x y (h l / g)) j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«redAt_mem_ampleBase» := P2M_GroundTheory_Heights__Heights_Kleiman_redAt_mem_ampleBase_2c1c57eb988c
