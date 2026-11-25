-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_prod_dvd_of_primes_e23e47e272ee
-- name    : P2M_GroundTheory_Heights__Heights_AntisymDivisible_prod_dvd_of_primes_e23e47e272ee
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:24.661996+00:00
-- url     : https://prove2.me/theorems/73e4bbf1-d535-402a-9dff-f72c41fc5c35
-- title:
--   P2 M Ground Theory Heights  Heights Antisym Divisible prod dvd of primes e23e47e272ee: P2 M Ground Theory Heights  Heights Antisym Divisible prod dvd of primes e23e47e272ee
-- statement:
--   The P2 M Ground Theory Heights  Heights Antisym Divisible prod dvd of primes e23e47e272ee construction uses the P2 M Ground Theory Heights  Heights Antisym Divisible prod dvd of primes e23e47e272ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L129-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L129-L150

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymDivisible
variable {σ : Type*} [DecidableEq σ]

theorem P2M_GroundTheory_Heights__Heights_AntisymDivisible_prod_dvd_of_primes_e23e47e272ee {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ)
    (P : MvPolynomial σ ℝ) (hp : ∀ i ∈ s, Prime (f i))
    (hnd : ∀ i ∈ s, ∀ k ∈ s, i ≠ k → ¬ f i ∣ f k) (hd : ∀ i ∈ s, f i ∣ P) :
    ∏ i ∈ s, f i ∣ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AntisymDivisible».«prod_dvd_of_primes» := P2M_GroundTheory_Heights__Heights_AntisymDivisible_prod_dvd_of_primes_e23e47e272ee
