-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_sum_freeIncl_freeCoord_02308404be61
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_sum_freeIncl_freeCoord_02308404be61
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:30:10.253809+00:00
-- url     : https://prove2.me/theorems/b0511139-5479-4e25-963f-f1b77cb6312d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman sum free Incl free Coord 02308404be61: P2 M Ground Theory Heights  Heights Kleiman sum free Incl free Coord 02308404be61
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman sum free Incl free Coord 02308404be61 construction uses the P2 M Ground Theory Heights  Heights Kleiman sum free Incl free Coord 02308404be61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreFree.lean#L162-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreFree.lean#L162-L191

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreFree
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
universe u v w
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
variable (𝓜 : GradedPMod S N M) {r : ℕ} (b : Module.Basis (Fin r) (Poly S N) M) (d : Fin r → ℤ)
variable (hb : ∀ j, b j ∈ 𝓜.piece (d j))
include hb

theorem P2M_GroundTheory_Heights__Heights_Kleiman_sum_freeIncl_freeCoord_02308404be61 (i : ℕ) (c : ℤ) (x : cohom 𝓜 i c) :
    ∑ j, freeIncl 𝓜 b d hb i c j (freeCoord 𝓜 b d hb i c j x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«sum_freeIncl_freeCoord» := P2M_GroundTheory_Heights__Heights_Kleiman_sum_freeIncl_freeCoord_02308404be61
