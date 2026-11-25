-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_one_mem_idealMod_30c22dbb3514
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_one_mem_idealMod_30c22dbb3514
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:01:05.643475+00:00
-- url     : https://prove2.me/theorems/81891c31-71d5-4d8f-bdcd-8b1c41be7034
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid one mem ideal Mod 30c22dbb3514: P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid one mem ideal Mod 30c22dbb3514
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid one mem ideal Mod 30c22dbb3514 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid one mem ideal Mod 30c22dbb3514 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplaneMid.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplaneMid.lean#L94-L97

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_one_mem_idealMod_30c22dbb3514 {pp : Ideal (Poly k N)} {I : Chart x} {l : Fin (N + 1)} (hl : l ∈ I.1)
    (hX : (X l : Poly k N) ∈ pp) : (1 : Ω) ∈ idealMod pp I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperHyperplaneMid».«one_mem_idealMod» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_one_mem_idealMod_30c22dbb3514
