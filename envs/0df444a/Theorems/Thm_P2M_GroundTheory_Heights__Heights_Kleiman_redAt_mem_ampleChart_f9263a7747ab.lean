-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redAt_mem_ampleChart_f9263a7747ab
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_redAt_mem_ampleChart_f9263a7747ab
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:04:07.92298+00:00
-- url     : https://prove2.me/theorems/19cbcac6-0543-4c72-a5b1-8c92b5e24970
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman red At mem ample Chart f9263a7747ab: P2 M Ground Theory Heights  Heights Kleiman red At mem ample Chart f9263a7747ab
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman red At mem ample Chart f9263a7747ab construction uses the P2 M Ground Theory Heights  Heights Kleiman red At mem ample Chart f9263a7747ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L168-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L168-L186

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_redAt_mem_ampleChart_f9263a7747ab (hg : RedGood hxy Nb.toSubSystem g) (Q' : LineBundle k y)
    (hQ : Q'.toSubSystem = redSys hxy Nb.toSubSystem g) (hσ : σ / g ∈ locAt k x y)
    (hσr : redAt k x y (σ / g) ≠ 0) (I : Chart y) {c : Ω}
    (hc : c ∈ ampleChart Nb.toSubSystem 1 σ (liftChart hxy I)) :
    c ∈ locAt k x y ∧ redAt k x y c ∈ ampleChart Q'.toSubSystem 1 (redAt k x y (σ / g)) I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«redAt_mem_ampleChart» := P2M_GroundTheory_Heights__Heights_Kleiman_redAt_mem_ampleChart_f9263a7747ab
