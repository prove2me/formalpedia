-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_secIdeal_map_7adffbdf0ec9
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_secIdeal_map_7adffbdf0ec9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:53.290791+00:00
-- url     : https://prove2.me/theorems/1987698e-bf4d-4e95-b906-284a8c066266
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec Alg Field Change sec Ideal map 7adffbdf0ec9: P2 M Ground Theory Heights  Heights Vertical Sec Alg Field Change sec Ideal map 7adffbdf0ec9
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec Alg Field Change sec Ideal map 7adffbdf0ec9 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec Alg Field Change sec Ideal map 7adffbdf0ec9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecAlgFieldChange.lean#L54-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecAlgFieldChange.lean#L54-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecAlgFieldChange
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
open scoped TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecAlgFieldChange

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_secIdeal_map_7adffbdf0ec9 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n e : ℕ}
    (Q₀ : Ideal (MvPolynomial (Fin n) R)) (y₀ : Par e n → R) :
    secIdeal (Q₀.map (MvPolynomial.map φ)) (φ ∘ y₀) =
      (secIdeal Q₀ y₀).map (MvPolynomial.map φ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecAlgFieldChange».«secIdeal_map» := P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_secIdeal_map_7adffbdf0ec9
