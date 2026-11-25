-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ne_zero_of_redAt_div_388ce3c8bed3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ne_zero_of_redAt_div_388ce3c8bed3
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:56:57.23998+00:00
-- url     : https://prove2.me/theorems/566dd375-ae11-58e5-89cf-3f13172fa95f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ne zero of red At div 388ce3c8bed3: P2 M Ground Theory Heights  Heights Kleiman ne zero of red At div 388ce3c8bed3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ne zero of red At div 388ce3c8bed3 construction uses the P2 M Ground Theory Heights  Heights Kleiman ne zero of red At div 388ce3c8bed3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L165-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L165-L166

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ne_zero_of_redAt_div_388ce3c8bed3 (hσ : σ / g ∈ locAt k x y) (hσr : redAt k x y (σ / g) ≠ 0) : σ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ne_zero_of_redAt_div» := P2M_GroundTheory_Heights__Heights_Kleiman_ne_zero_of_redAt_div_388ce3c8bed3
