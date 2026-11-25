-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redSys_sub_eq_ebff74c5b356
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_redSys_sub_eq_ebff74c5b356
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:10:05.418647+00:00
-- url     : https://prove2.me/theorems/cfe92e0c-6844-4a9a-9582-c7b663746be5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman red Sys sub eq ebff74c5b356: P2 M Ground Theory Heights  Heights Kleiman red Sys sub eq ebff74c5b356
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman red Sys sub eq ebff74c5b356 construction uses the P2 M Ground Theory Heights  Heights Kleiman red Sys sub eq ebff74c5b356 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L83-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L83-L106

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_redSys_sub_eq_ebff74c5b356 (hV : IsVeryAmpleBy Nb.toSubSystem h) (hg : RedGood hxy Nb.toSubSystem g)
    (I : Chart y) : (redSys hxy Nb.toSubSystem g).sub I =
      Submodule.span (chartRing k y I) (Set.range fun l => redAt k x y (h l / g)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«redSys_sub_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_redSys_sub_eq_ebff74c5b356
