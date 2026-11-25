-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_subset_support_of_redAt_ne_zero_a576846f447b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_subset_support_of_redAt_ne_zero_a576846f447b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:10:44.888716+00:00
-- url     : https://prove2.me/theorems/1cff1bf5-f294-4c01-a317-7afd3446c3d5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman subset support of red At ne zero a576846f447b: P2 M Ground Theory Heights  Heights Kleiman subset support of red At ne zero a576846f447b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman subset support of red At ne zero a576846f447b construction uses the P2 M Ground Theory Heights  Heights Kleiman subset support of red At ne zero a576846f447b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L227-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L227-L272

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_subset_support_of_redAt_ne_zero_a576846f447b (hg : RedGood hxy Nb.toSubSystem g)
    (hσ : σ / g ∈ locAt k x y) (hσr : redAt k x y (σ / g) ≠ 0) (I₀ : Chart y) {b : Ω}
    (hb : b ∈ locAt k x y) (hbr : redAt k x y b ≠ 0) {J : Chart x}
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart Nb.toSubSystem 1 σ I) :
    J.1 ⊆ support y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«subset_support_of_redAt_ne_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_subset_support_of_redAt_ne_zero_a576846f447b
