-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_eval_specRest_c1d6a2947cb7
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_eval_specRest_c1d6a2947cb7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:46.356744+00:00
-- url     : https://prove2.me/theorems/956197fa-9426-4984-ae95-f8a5f038e47b
-- title:
--   P2 M Ground Theory Heights  Heights Vertical eval spec Rest c1d6a2947cb7: P2 M Ground Theory Heights  Heights Vertical eval spec Rest c1d6a2947cb7
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical eval spec Rest c1d6a2947cb7 construction uses the P2 M Ground Theory Heights  Heights Vertical eval spec Rest c1d6a2947cb7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecLinNZD.lean#L12-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecLinNZD.lean#L12-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSpecFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecLinNZD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Vertical_eval_specRest_c1d6a2947cb7 {k E : Type*} [CommRing k] [CommRing E] (φ : k →+* E) {n e : ℕ}
    (g : MvPolynomial (Fin (e + 1) × Fin n) k) (y : Par e n → E) (u : Fin n → k) :
    eval (fun j => φ (u j)) (specRest φ g y) =
      eval₂ φ (fun ij : Fin e × Fin n => y (.inl ij)) (specFirst g u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«eval_specRest» := P2M_GroundTheory_Heights__Heights_Vertical_eval_specRest_c1d6a2947cb7
