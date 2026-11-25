-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_restrictData_redSys_99a0dcef8017
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_restrictData_redSys_99a0dcef8017
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:57:30.189426+00:00
-- url     : https://prove2.me/theorems/c3f42a99-2270-575f-a0b3-9e44494b147b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman restrict Data red Sys 99a0dcef8017: P2 M Ground Theory Heights  Heights Kleiman restrict Data red Sys 99a0dcef8017
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman restrict Data red Sys 99a0dcef8017 construction uses the P2 M Ground Theory Heights  Heights Kleiman restrict Data red Sys 99a0dcef8017 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L149-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L149-L161

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_restrictData_redSys_99a0dcef8017 (hg : RedGood hxy Nb.toSubSystem g) (Q' : LineBundle k y)
    (hQ : Q'.toSubSystem = redSys hxy Nb.toSubSystem g) :
    RestrictData Nb.toSubSystem hxy Q'.toSubSystem (fun q => redAt k x y (q / g)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«restrictData_redSys» := P2M_GroundTheory_Heights__Heights_Kleiman_restrictData_redSys_99a0dcef8017
