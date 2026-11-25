-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_eulerCharQuot_eq_of_mul_006227a8d564
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_eulerCharQuot_eq_of_mul_006227a8d564
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:43.28192+00:00
-- url     : https://prove2.me/theorems/2e0c963d-d8fe-45a8-ad43-c86e824ab93d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid euler Char Quot eq of mul 006227a8d564: P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid euler Char Quot eq of mul
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid euler Char Quot eq of mul 006227a8d564 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid euler Char Quot eq of mul 006227a8d564 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplaneMid.lean#L27-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplaneMid.lean#L27-L59

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_eulerCharQuot_eq_of_mul_006227a8d564 (F₁ F₂ G₁ G₂ : SubSystem k x Ω) (u : Ω)
    (hmap : ∀ I, ∀ y ∈ F₁.sub I, u * y ∈ G₁.sub I)
    (honto : ∀ I, ∀ z ∈ G₁.sub I, ∃ y ∈ F₁.sub I, z - u * y ∈ G₂.sub I)
    (hker : ∀ I, ∀ y ∈ F₁.sub I, u * y ∈ G₂.sub I ↔ y ∈ F₂.sub I) :
    eulerCharQuot k G₁ G₂ = eulerCharQuot k F₁ F₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperHyperplaneMid».«eulerCharQuot_eq_of_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_eulerCharQuot_eq_of_mul_006227a8d564
