-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_eulerCharQuot_mid_6a0fa6ff4b63
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_eulerCharQuot_mid_6a0fa6ff4b63
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:58:28.703532+00:00
-- url     : https://prove2.me/theorems/66aa158e-9dca-48dd-a43f-b433fb11bd6f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid euler Char Quot mid 6a0fa6ff4b63: P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid euler Char Quot mid 6a0fa6ff4b63
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid euler Char Quot mid 6a0fa6ff4b63 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid euler Char Quot mid 6a0fa6ff4b63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplaneMid.lean#L161-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplaneMid.lean#L161-L224

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_eulerCharQuot_mid_6a0fa6ff4b63 (pp : Ideal (Poly k N)) (hp : pp.IsPrime)
    (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) (hle : primeOf (S := k) x ≤ pp)
    (i : Fin (N + 1)) (hi : (X i : Poly k N) ∉ pp) (M : SubSystem k x Ω)
    (hM : ∀ I, ∃ M' : Submodule (chartRing k x I) Ω, M.sub I * M' = 1) :
    eulerCharQuot k ((M.twist (twistSys k x 1)).twist (idealSys x (pp ⊔ Ideal.span {(X i : Poly k N)})))
        ((M.twist (twistSys k x 1)).twist (idealSys x pp)) =
      eulerCharQuot k M (M.twist (idealSys x pp)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperHyperplaneMid».«eulerCharQuot_mid» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_eulerCharQuot_mid_6a0fa6ff4b63
