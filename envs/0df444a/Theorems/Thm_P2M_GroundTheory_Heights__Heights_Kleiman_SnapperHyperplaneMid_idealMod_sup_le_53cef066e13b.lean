-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_idealMod_sup_le_53cef066e13b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_idealMod_sup_le_53cef066e13b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:58:57.631304+00:00
-- url     : https://prove2.me/theorems/20104460-f5df-43a8-9a48-02f65cf84580
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid ideal Mod sup le 53cef066e13b: P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid ideal Mod sup le 53cef066e13b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid ideal Mod sup le 53cef066e13b construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid ideal Mod sup le 53cef066e13b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplaneMid.lean#L131-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplaneMid.lean#L131-L159

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_idealMod_sup_le_53cef066e13b {pp : Ideal (Poly k N)} (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp)
    {i j : Fin (N + 1)} {I : Chart x} (hj : j ∈ I.1) :
    idealMod (pp ⊔ Ideal.span {(X i : Poly k N)}) I ≤
      idealMod pp I ⊔ Submodule.span (chartRing k x I) {x i / x j} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperHyperplaneMid».«idealMod_sup_le» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_idealMod_sup_le_53cef066e13b
