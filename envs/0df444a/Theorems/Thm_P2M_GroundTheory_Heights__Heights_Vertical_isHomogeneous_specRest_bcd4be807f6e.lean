-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_isHomogeneous_specRest_bcd4be807f6e
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_isHomogeneous_specRest_bcd4be807f6e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:35.127033+00:00
-- url     : https://prove2.me/theorems/eff4455f-64f9-47b8-8d0b-2e28f49b66dc
-- title:
--   P2 M Ground Theory Heights  Heights Vertical is Homogeneous spec Rest bcd4be807f6e: P2 M Ground Theory Heights  Heights Vertical is Homogeneous spec Rest bcd4be807f6e
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical is Homogeneous spec Rest bcd4be807f6e construction uses the P2 M Ground Theory Heights  Heights Vertical is Homogeneous spec Rest bcd4be807f6e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChowSecDegree.lean#L12-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChowSecDegree.lean#L12-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormEval
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowSecDegree
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

theorem P2M_GroundTheory_Heights__Heights_Vertical_isHomogeneous_specRest_bcd4be807f6e {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n e d : ℕ}
    {g : MvPolynomial (Fin (e + 1) × Fin n) R} (hg : IsMultiHomog d g) (y : Par e n → S) :
    (specRest φ g y).IsHomogeneous d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«isHomogeneous_specRest» := P2M_GroundTheory_Heights__Heights_Vertical_isHomogeneous_specRest_bcd4be807f6e
