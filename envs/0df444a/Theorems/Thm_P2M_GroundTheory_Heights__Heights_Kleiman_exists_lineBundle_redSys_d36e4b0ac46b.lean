-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_lineBundle_redSys_d36e4b0ac46b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_lineBundle_redSys_d36e4b0ac46b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:03:10.470168+00:00
-- url     : https://prove2.me/theorems/b814b5d2-ae59-4c8d-8176-d368ec8685bd
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists line Bundle red Sys d36e4b0ac46b: P2 M Ground Theory Heights  Heights Kleiman exists line Bundle red Sys d36e4b0ac46b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists line Bundle red Sys d36e4b0ac46b construction uses the P2 M Ground Theory Heights  Heights Kleiman exists line Bundle red Sys d36e4b0ac46b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L108-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L108-L147

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_lineBundle_redSys_d36e4b0ac46b (hV : IsVeryAmpleBy Nb.toSubSystem h) (hg0 : g ≠ 0)
    (hg : RedGood hxy Nb.toSubSystem g) (hgsec : ∀ I : Chart x, g ∈ Nb.sub I) :
    ∃ Q' : LineBundle k y, Q'.toSubSystem = redSys hxy Nb.toSubSystem g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_lineBundle_redSys» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_lineBundle_redSys_d36e4b0ac46b
