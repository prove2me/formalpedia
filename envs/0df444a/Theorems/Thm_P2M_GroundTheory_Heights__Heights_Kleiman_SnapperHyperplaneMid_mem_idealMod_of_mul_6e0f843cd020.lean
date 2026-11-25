-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_mem_idealMod_of_mul_6e0f843cd020
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_mem_idealMod_of_mul_6e0f843cd020
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:23:09.706841+00:00
-- url     : https://prove2.me/theorems/4db8ef0b-0ceb-48b8-8792-7e07544afd40
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid mem ideal Mod of mul 6e0f843cd020: P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid mem ideal Mod of mul 6e0f843cd0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid mem ideal Mod of mul 6e0f843cd020 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid mem ideal Mod of mul 6e0f843cd020 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplaneMid.lean#L99-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplaneMid.lean#L99-L129

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDevissage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplaneMid
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
open GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_mem_idealMod_of_mul_6e0f843cd020 {pp : Ideal (Poly k N)} (hp : pp.IsPrime) (hle : primeOf (S := k) x ≤ pp)
    {i j : Fin (N + 1)} (hi : (X i : Poly k N) ∉ pp) {I : Chart x} {r q : Ω} (hr : r ∈ chartRing k x I)
    (hq : q ∈ idealMod pp I) (h : x i * r = x j * q) : r ∈ idealMod pp I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperHyperplaneMid».«mem_idealMod_of_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_mem_idealMod_of_mul_6e0f843cd020
