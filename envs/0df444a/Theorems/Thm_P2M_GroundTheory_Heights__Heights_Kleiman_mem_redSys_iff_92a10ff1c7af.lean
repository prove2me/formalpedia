-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_redSys_iff_92a10ff1c7af
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_redSys_iff_92a10ff1c7af
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:38:34.034823+00:00
-- url     : https://prove2.me/theorems/0aab20f0-b17d-5634-a53a-4bd04ab84e5a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem red Sys iff 92a10ff1c7af: P2 M Ground Theory Heights  Heights Kleiman mem red Sys iff 92a10ff1c7af
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem red Sys iff 92a10ff1c7af construction uses the P2 M Ground Theory Heights  Heights Kleiman mem red Sys iff 92a10ff1c7af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionSystems.lean#L35-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionSystems.lean#L35-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
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
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_redSys_iff_92a10ff1c7af {P : SubSystem k x Ω} {γ : Ω} (hP : RedGood hxy P γ) (I : Chart y) (z : K') :
    z ∈ (redSys hxy P γ).sub I ↔ ∃ q ∈ P.sub (liftChart hxy I), redAt k x y (q / γ) = z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_redSys_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_redSys_iff_92a10ff1c7af
